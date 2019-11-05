#lang scribble/base

@(require (prefix-in r: "redex/sub.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λsub)
@define[λsub]{@langname[λ-sub]}

@title{@|λsub|: subtyping with records}

@section[#:tag "λsub-syntax"]{Syntax}

Extending STLC with records is straightforward. First, we extend
the syntax of types and terms, using @term[l] for record field labels:
@;
@render-nonterminals[r:λsub t e l m]

A record type
lists field names with their types; assume the field names are not repeated
within a record. A record expression lists field names with expressions
whose values will fill the fields. A projection expression projects the
value of the named field from a record.

@section[#:tag "λsub-dynamics"]{Dynamic semantics}

The dynamics are straightforward. We extend values to include records where
every field contains a value. We extend evaluation contexts to evaluate
the fields of a record from left to right.
@;
@render-nonterminals[r:λsub v E].

Then we add one reduction rule, for projecting the field from a record:
@;
@render-reduction-rules[r:->val prj]

@section[#:tag "λsub-statics"]{Static semantics}

The simplest way to type records is to add one rule for each new
expression form and keep the rest of the language the same:
@;
@render-judgment-rules[r:types record project]

This works, but it’s not as expressive as we might like. Consider a function
@term[(λ x (Record [l nat]) (project x l))]. It takes a record of one field
@term[l] and projects out that field. But is there any reason we shouldn't be
able to use this function on a record with @emph{more} fields than @term[l]?
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
(depth subtyping). We can express this with three rules:
@;
@render-judgment-rules[r:<: rec-empty rec-width rec-depth]
@;
Rule @rulename[rec-empty] says that the empty record is a subtype of
itself; we need this as a base case.
Rule @rulename[rec-width] says that supertype records may have fields
that are missing from their subtypes.
Rule @rulename[rec-depth] says that when records have a common member
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

@subsection[#:tag "λsub-safety"]{Type safety}

Subtyping changes our preservation theorem somewhat, because
reduction can cause type refinement. (That is, we learn more type
information.) Here is the updated preservation theorem:

@theorem[#:name "Preservation"]{If @term[(types • e_1 t_1)] and
 @term[(--> e_1 e_2)] then there exists some @term[t_2] such that
 @term[(types • e_2 t_2)] and @term[(<: t_2 t_1)].}

Before we can prove it, we update the replacement and substitution lemmas
as follows:

@lemma[#:name "Replacement"]{If @term[(types Γ (in-hole E e) t)], then
 @term[(types Γ e t_e)] for some type @term[t_e]. Furthermore, for any
 @term[e_new] such that @term[(types Γ e_new t_new)] for @term[(<: t_new t_e)],
 @term[(types Γ (in-hole E e_2) t_out)] for some @term[t_out] such that
 @term[(<: t_out t)].}

@proof[] By induction on @term[E]. The interesting cases are for application:

@itemlist[
 @item{If @term[E] is @term[(ap E_1 e_2)] then the whole term has a type
  @term[t] only if there are some types @term[t_1] and @term[t_2] such that
  @term[(types • (in-hole E_1 e) (-> t_1 t))] and
  @term[(types • e_2 t_2)] where
  @term[(<: t_2 t_1)]. Then by induction, @term[e] has a type, and if we
  replace @term[e] with @term[e_new] having a subtype of that, then
  @term[(types • (in-hole E_1 e_new) t_^†)] for
  @term[(<: t_^† (-> t_1 t))]. The subtyping relation relates arrows only to
  other arrows, so @term[t_^†] = @term[(-> t_1^† t_2^†)] with
  @term[(<: t_1 t_1^†)] and @term[(<: t_2^† t)]. Then by transitivity,
  @term[(<: t_2 t_1^†)]. This means that we can reform the application
  @term[(types • (ap (in-hole E_1 e_new) e_2) t_2^†)], which has a subtype of
  @term[t].}
 @item{If @term[E] is @term[(ap e_1 E_2)], then the whole term has a type
  @term[t] only if there are some types @term[t_1] and @term[t_2] such that
  @term[(types • e_1 (-> t_1 t))] and
  @term[(types • (in-hole E_2 e) t_2)] where
  @term[(<: t_2 t_1)].
  Then by induction, @term[e] has a type, and if we replace @term[e] with
  @term[e_new] having a subtype of that, then
  @term[(types • (in-hole E_2 e_new) t_2^†)] where @term[(<: t_2^† t_2)].
  Then by transitivity, @term[(<: t_2^† t_1)], so we can reform the application
  having the same type @term[t].}
]

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
  @term[(ap (substitute e_11 x e_1) (substitute e_12 x e_1))]
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

 @item{If @term[(--> (in-hole E (project (record [l_i v_i] ... [l v] [l_j v_j] ...) l)) (in-hole E v))],
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
 @item{If @term[t] is @term[(Record [l t_1] ...)], then @term[v] is a record
          with at least the fields @term[l].}
]

@proof[] By induction on the structure of the typing derivation. Only four
rules form values, and those rules correspond to the conditions of the lemma.

@lemma[#:name "Progress"]{
  If @term[(types • e_1 t)] then either @term[e_1] is a value or
     @term[(--> e_1 e_2)] for some term @term[e_2].
}

@proof[] By induction on the typing derivation:

@itemlist[
 @item{@term[(types • x t)] is vacuous.}
 @item{@term[(types • z nat)] is a value.}
 @item{If @term[(types • (s e) nat)] then by inversion,
  @term[(types • e nat)]. Then by induction, @term[e] either takes a step
  or is a value. If it's a value, then @term[(s e)] is a value; if it takes
  a step to @term[e_^†] then @term[(s e)] takes a step to @term[(s e_^†)].}
 @item{If @term[(types • (ap e_11 e_12) t)] then by inversion,
  @term[(types • e_11 (-> t_11 t))] and @term[(types • e_12 t_12)] for some
  types @term[t_11] and @term[t_12] such that @term[(<: t_12 t_11)].
  Then by induction, each of @term[e_11] and @term[e_12]
  either is a value or takes a step. If @term[e_11] takes a step to
  @term[e_11^†], then the whole term takes a step to @term[(ap e_11^† e_12)].
  If @term[e_11] is a value @term[v_11] and @term[e_12] takes a step to
  @term[e_12^†], then the whole term takes a step to @term[(ap v_11 e_12^†)].
  Otherwise, @term[e_12] is a value @term[v_12]. By the canonical forms
  lemma, @term[v_11] has the form @term[(λ x t_11 e_111)]. Then the whole
  term takes a step to @term[(substitute e_111 x v_12)].}
 @item{@term[(types • (λ x t_1 e) (-> t_1 t_2))] is a value.}
 @item{If @term[(types • (record [l_i e_i] ...) (Record l_i t_i))] then
  by inversion, @term[(types • e_i t_i)] for all @term[e_i]. Then
  by induction, each of those takes a step or is a value. If any takes
  a step, then the whole term steps by the leftmost @term[e_i] to take
  a step. Otherwise, they are all values, and the whole term is a value.}
 @item{If @term[(types • (project e l) t_f)] then by inversion,
  @term[e] has a record type with a field @term[l] having type
  @term[t_f]. By induction, @term[e] either takes a step or is a value @term[v].
  If it takes a step then the whole term takes a step. If it's a value,
  then by the canonical forms lemma, it's a value
  @term[(record [l_i v_i] ... [l v_f] [l_j v_j] ...)]. Then the whole term
  takes a step to @term[v_f].}
]

@theorem[#:name "Type safety"] @λsub is type safe.

@proof[] By progess and preservation.

@section[#:tag "λsub-coercion"]{Compiling with coercions}

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

The empty record is a supertype of itself, by the identity coercion:
@;
@render-judgment-rules[r:<:~> rec-empty]

In subtyping records, we can skip fields and not include them in the supertype:
@;
@render-judgment-rules[r:<:~> rec-width]

The depth-subyping record case is hairy. We convert record types by converting
one element and then recursively converting the rest of the record, and then
reassembling the desired result:
@;
@render-judgment-rules[r:<:~> rec-depth]

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

@exercise{Define a Point as a record with fields x and y, which are
integers. Define a ColorPoint as a Point with an additional field, the
color, which is a string. Define a function that takes a Point. Show
that your function can be used on a ColorPoint.}
