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

@subsection[#:tag "λsub-soundness"]{Type Soundness of @|λsub|.}

Subtyping changes our preservation theorem somewhat, because
reduction can cause type refinement. (That is, we learn more type
information.) Here is the updated preservation theorem:

@theorem[#:name "Preservation"]{If @term[(types • e_1 t_1)] and
 @term[(--> e_1 e_2)] then there exists some @term[t_2] such that
 @term[(types • e_2 t_2)] and @term[(<: t_2 t_1)].}

Before we can prove it, we update the substitution lemma as follows:

@lemma[#:name "Substitution"]{If @term[(types Γ e_1 t_1)]
 and @term[(types (extend Γ x t_1^†) e_2 t_2)] where
 @term[(<: t_1 t_1^†)]
then @term[(types Γ (substitute e_2 x e_1) t_2^†)]
for @term[(<: t_2^† t_2)].}

@proof[] By induction on the derivation of the typing of @term[e_2]:

@itemlist[
 @item{@term[(types (extend Γ x t_1^†) y t_2)].

  If @term[x] = @term[y], then @term[t_2] = @term[t_1^†].
  Then @term[(substitute e_2 x e_1)] = @term[e_1], which has type @term[t_1].
  Let @term[t_2^†] be @term[t_1]. Then the subtyping holds.

  If @term[x] ≠ @term[y], then @term[(types (extend Γ x t_1^†) y (lookup Γ y))],
  as before the substitution.}

 @item{@term[(types (extend Γ x t_1^†) z nat)], then substitution has no
  effect and it types in any environment.}

 @item{@term[(types (extend Γ x t_1^†) (s e) nat)], then by induction
        @term[(types Γ (substitute e x e_1) nat)], which relates
        only to @term[nat]. Then reapply @term[s].}

 @item{@term[(types (extend Γ x t_1^†) (λ y t_11 e) (-> t_11 t_12))],
  then by inversion we know that
  @term[(types (extend (extend Γ x t_1^†) y t_11) e t_12)].
  Then by the induction hypothesis,
  @term[(types (extend Γ y t_11) (substitute e x e_1) t_12^†)]
  for some @term[(<: t_12^† t_12)]. Then by @rulename[abs],
  @term[(types Γ (substitute (λ y t_11 e) x e_1) (-> t_11 t_12^t))],
  which is a subtype of @term[(-> t_11 t_12)].}

 @item{@term[(types (extend Γ x t_1^†) (ap e_11 e_12) t_1)], then by
  inversion we know that
  @term[(types (extend Γ x t_1^†) e_11 (-> t_11 t_1))] and
  @term[(types (extend Γ x t_1^†) e_12 t_12)] where
  @term[(<: t_12 t_11)].
  Then by induction (twice), we have that
  @term[(types Γ (substitute e_11 x e_1) t_11^†)] where
  @term[(<: t_11^† (-> t_11 t_1))] and that
  @term[(types Γ (substitute e_12 x e_1) t_12^†)] where
  @term[(<: t_12^† t_12)].
  By inspection of the subtype relation, the only types related to arrow types
  are arrow types, so @term[t_11^†] must be an arrow type
  @term[(-> t_111^† t_112^†)] where @term[(<: t_11 t_111^†)]
  and @term[(<: t_112^† t_1)].
  Then by transitivity (twice),
  @term[(<: t_12^† t_111^†)]. This means we can apply
  @term[(ap (substitute e_11 x e_1) (substitute e_12 x e_2))]
  yielding type @term[t_112^†], which is a subtype of @term[t_1].}

 @item{The record construction and projection cases are straightforward.}
]

@proof[#:name "of preservation"]
By cases on the reduction relation. There are two cases:

@itemlist[
 @item{If @term[(--> (in-hole E (ap (λ x t_1 e_1) v_2)) (in-hole E (substitute e_1 x v_2)))],
  then by replacement, @term[(ap (λ x t_1 e_1) v_2)] has a type, and it suffices
  to show that this type is preserved.
  Then by inversion (twice), we know that
  @term[(types (extend • x t_1) e_1 t)]
  and @term[(types • v_2 t_2)] where @term[(<: t_2 t_1)].
  Then by the substitution lemma,
  @term[(types • (substitute e_1 x v_2) t_^†)] where
  @term[(<: t_^† t)].}

 @item{If @term[(--> (in-hole E (project (record [f_i v_i] ... [f v] [f_j v_j] ...) f)) (in-hole E v))],
  this case is straightforward.}
]

QED.

@lemma[#:name "Canonical forms"]

If @term[(types • v t)], then:

@itemlist[
 @item{If @term[t] is @term[nat], then @term[v] is either @term[z]
          or @term[(s v_1)].}
 @item{If @term[t] is @term[(-> t_1 t_2)], then @term[v] has the form
          @term[(λ x t_1 e)].}
 @item{If @term[t] is @term[(Record [f t_1] ...)], then @term[v] is a record
          with at least the fields @term[f].}
]

@lemma[#:name "Progress"]{
  If @term[(types • e_1 t)] then either @term[e_1] is a value or
     @term[(--> e_1 e_2)] for some term @term[e_2].
}

@subsection[#:tag "λsub-coercion"]{Compiling with Coercions}

To say that @term[(<: t_1 t_2)] is to say that a @term[t_1] can be used
wherever a @term[t_2] is expected, but do our run-time representations actually
make that true? In some languages yes, but in many languages no. We might not
want, for example, for record operations to have to do a (linear) search of
field names at run time, but instead to fix the offset at compile time. Such
a representation choice is not incompable with subtyping, if we are willing to
interpret subtyping as a coercion between potentially different underlying
representation types. For example, record type
@term[(Record [a t_a] [b t_b] [c t_c])] is a subtype of
record type
@term[(Record [a t_a] [c t_c])]. The former is represented by a 3-element vector
containing the values of fields a, b, and c, whereas the rather is represented
as a 2-element vector containing the values of fields a and c. We cannot use an
instance of the former as the latter directly, but we can coerce it. The
coercion between two types in the subtype relationship is witnessed by the
function converting the subtype to the supertype.

In particular, the witness to the fact that @term[(<: nat nat)] is the identity
function on type @term[nat]:
@;
@render-judgment-rules[r:<:~> nat]

To witness an arrow subtyping, we build a function that applies the witness
to the domain coercion to the argument and the witness to the codomain coercion
to the result of the coerced function:
@;
@render-judgment-rules[r:<:~> arr]

The empty record is a supertype of every record because we can take any record
and produce the empty record:
@;
@render-judgment-rules[r:<:~> rec-nil]

The non-empty record case is hairy. We convert record types by converting
one element and then recursively converting the rest of the record, and then
reassembling the desired result:
@;
@render-judgment-rules[r:<:~> rec-cons]

The typing rules now translate from a language with subtyping to a language
that doesn't use subtyping. All of the rules except @rulename[app] just
translate each term by homomorphically translating the subterms:
@;
@render-judgment-rules[r:types~> var zero succ record project abs]

The only interesting rule is @rulename[app], which includes subtyping. It
generates the coercion for the particular subtyping used, and then applies that
to coerce the argument to the function:
@;
@render-judgment-rules[r:types~> app]

