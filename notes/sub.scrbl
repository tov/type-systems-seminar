#lang scribble/base

@(require (prefix-in r: "redex/sub.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λsub)
@define[λsub]{@langname[λsub]}

@title{@|λsub|: Subtyping with Records}

@section[#:tag "λsub-syntax"]{Syntax}

Extending STLC with records is straightforward. First, we extend
the syntax of types and terms, using @term[f] for record field labels:
@;
@render-nonterminals[r:λsub t e f]

A record type
lists field names with their types; assume the field names are not repeated
within a record. A record expression lists field names with expressions
whose values will fill the fields. A projection expression projects the
value of the named field from a record.

@section[#:tag "λsub-dynamics"]{Dynamic Semantics}

The dynamics are straightforward. We extend values to include records where
every field contains a value. We extend evaluation contexts to evaluate
the fields of a record from left to right.
@;
@render-nonterminals[r:λsub v E].

Then we add one reduction rule, for projecting the field from a record:
@;
@render-reduction-rules[r:->val prj]

@section[#:tag "λsub-statics"]{Static Semantics}

The simplest way to type records is to add one rule for each new
expression form and keep the rest of the language the same:
@;
@render-judgment-rules[r:types record project]

This works, but it’s not as expressive as we might like. Consider a function
@term[(λ x (Record [f nat]) (project x f))]. It takes a record of one field
@term[f] and projects out that field. But is there any reason we shouldn't be
able to use this function on a record with @emph{more} fields than @term[f]?
Subtyping captures that intuition, allowing us to formalize it and prove it
sound.

@subsection[#:tag "λsub-subtyping"]{Subtyping}

To do this, we define the subtype relation @term[<:], which related pairs of
types. Intuititively @term[(<: t_1 t_2)] means that a @term[t_1] may be used
wherever a @term[t_2] is required.

First, @term[nat] is a subtype of itself:
@;
@render-judgment-rules[r:<: nat]

Second, function types are contravariant in the domain and covariant in the
arguments:
@;
@render-judgment-rules[r:<: arr]

@exercise{Suppose that @term[(<: Int Real)]. Consider the types
 @term[(-> Int Int)], @term[(-> Real Real)], @term[(-> Int Real)], and
 @term[(-> Real Int)]. Which of these are subtypes of which others? Does
 this make sense?}

Finally, records provide subtyping by allowing the forgetting of fields
(this is called width subtyping) and by subtyping within individual fields
(depth subtyping). We can express this with two rules:
@;
@render-judgment-rules[r:<: rec-nil rec-cons]
@;
Rule @rulename[rec-nil] says that all records are subtypes of the empty
record. Rule @rulename[rec-cons] says that when records have a common member
then the types of the fields must be subtypes.

@exercise{Prove that @term[<:] is a preorder, that is, reflexive and
 transitive.}

The idea of subtyping is that we can apply it everywhere. If we can conclude
that @term[(types Γ e t_1)] and @term[(<: t_1 t_2)] then we should be able to
conclude that @term[(types Γ e t_2)]. It's possible to add such a rule, and
it works fine theoretically, but because the rule is not @emph{syntax directed},
it can be difficult to implement. In fact, the only place in our current
language that we need subtyping is in the application rule, so we replace
the STLC application rule with this:

@render-judgment-rules[r:types app]
