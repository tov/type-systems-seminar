#lang scribble/base

@(require (prefix-in r: "redex/stlc.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:stlc)
@define[stlc]{@langname[λ-st]}

@title{The Simply-Typed Lambda Calculus @stlc}

@section[#:tag "stlc-syntax"]{Syntax}

The @stlc language has types @term[t] and terms @term[e] defined as follows:

@render-nonterminals[r:stlc t e]

Types include the natural numbers @term[nat] and function types
@term[(-> t_1 t_2)]. Terms include variables, Peano naturals (@term[z] for
zero and @term[s] for successor), lambda abstractions, and applications.

@section[#:tag "stlc-dynamics"]{Dynamic Semantics}

To define the dynamic semantics of @stlc, we give syntax for values and
evaluation contexts:

@render-nonterminals[r:stlc v E].

Values include natural numbers and lambda abstractions. We evaluate under
@term[s] and we evaluate both the operator and operand in an application.

Then the reduction relation consists of one rule:

@render-reduction-rules[r:->val β-val]

@section[#:tag "stlc-statics"]{Static Semantics}

To type @stlc, we define typing contexts mapping variables to types:

@render-nonterminals[r:stlc Γ]

Then the rules are as follows. There are two constructors for the
naturals, and they type as such:
@;
@render-judgment-rules[r:types zero succ]
@;
That is, @term[z] is a natural, and for any term @term[e] of type @term[nat],
@term[(s e)] has type @term[nat] as well.

Variables type by looking them up in the typing context:
@;
@render-judgment-rules[r:types var]

Lambda abstractions type by extending the typing context with the bound variable
and checking the body:
@;
@render-judgment-rules[r:types abs]

And finally, applications require the domain of the operator to match the type
of the operand:
@;
@render-judgment-rules[r:types app]

@subsection[#:tag "stlc-type-safety"]{Type Safety}

Before we can prove type safety, we need to prove several standard lemmas.

We use the judgment @term[(types* e t)] with no context to mean that @term[e]
types in an empty context: @term[(types • e t)].

@lemma[#:name "Replacement"]{If @term[(types* (in-hole E e) t)] then
 @term[(types* e t_e)] for some @term[t_e]. Furthermore, for
 any other term @term[(types* e_new t_e)],
 @term[(types* (in-hole E e_new) t)].}

@proof[] By induction on the structure of @term[E]:

@itemlist[
 @item{@term[hole]: Then trivially, with @term[t_e] = @term[t].}
 @item{@term[(s E_1)]: By inspection of the typing rules, we know that if
  @term[(in-hole (s E_1) e)] has a type, that type is @term[int].
  By inversion, we know that @term[(in-hole E_1 e)] has type @term[int]
  as well. Then by the induction hypothesis, @term[e] has some type
  @term[t_e], and for any @term[e_new] having type @term[t_e],
  @term[(types* (in-hole E_1 e_new) int)]. Then by rule @rulename[succ],
  @term[(types* (s (in-hole E_1 e_new)) int)].}
 @item{@term[(ap E_1 e_1)]: The whole term has a type @term[t] only if
  there is some type @term[t_1] such that
  @term[(types* (in-hole E_1 e) (--> t_1 t))]
  and @term[(types* e_1 t_1)]. Then by the induction hypothesis,
  @term[(types* e t_e)], and for any term @term[e_new] having type
  @term[t_e], @term[(types* (in-hole E_1 e_new) (--> t_1 t))].
  Then @term[(types* (ap (in-hole E_1 e_new) e_1) t)].}
 @item{@term[(ap v_1 E_1)]: The whole term has a type @term[t] only if
  there is some type @term[t_1] such that
  @term[(types* v_1 (--> t_1 t))]
  and @term[(types* (in-hole E_1 e) t_1)]. Then by the induction hypothesis,
  @term[(types* e t_e)], and for any term @term[e_new] having type
  @term[t_e], @term[(types* (in-hole E_1 e_new) t_1)].
  Then @term[(types* (ap v_1 (in-hole E_1 e_new)) t)].}
]
               
@lemma[#:name "Substitution"]{If @term[(types Γ e_1 t_1)] and
 @term[(types (extend Γ x t_1) e_2 t_2)] then
 @term[(types Γ (substitute e_2 x e_1) t_2)].}

@proof[] By induction on the type derivation for @term[e_2]:

@itemlist[
 @item{@term[(types (extend Γ x t_1) y t_2)]: If @term[x] = @term[y] then
        @term[t_1] = @term[t_2], and @term[(substitute y x e_1)] =
        @term[e_1], which has type @term[t_1]. If @term[x] ≠ @term[y],
        then @term[(substitute y x e_1)] = @term[y], which must type
        in @term[Γ].}
 @item{@term[(types (extend Γ x t_1) z nat)]: This types in an environment.}
 @item{@term[(types (extend Γ x t_1) (s e) nat)]: Then it must be the case
        that @term[(types (extend Γ x t_1) e nat)]. Then by induction,
        @term[(types Γ (substitute e x e_1) nat)], and reapplying rule
        @rulename[succ], we have that
        @term[(types Γ (substituted (s e) x e_1) nat)].}
 @item{@term[ap] cases are similar.}
 @item{@term[(types (extend Γ x t_1) (λ y t_21 e) (-> t_21 t_22))]:
        This can be the case only if
        @term[(types (extend (extend Γ x t_1) y t_21) e t_22)]. Without
        loss of generality, @term[x] ≠ @term[y], so we can swap them,
        yielding
        @term[(types (extend (extend Γ y t_21) x t_1) e t_22)]. Then
        by induction
        @term[(types (extend Γ y t_21) (substitute e x e_1) t_22)].
        Then apply rule @rulename[abs], to get
        @term[(types Γ (substitute (λ y t_21 e) x e_1) (-> t_21 t_22))].}
]

@lemma[#:name "Preservation"]{If @term[(types* e_1 t)] and @term[(--> e_1 e_2)]
 then @term[(types* e_2 t)].}

@proof[] By cases on the reduction relation. There is one case:

@itemlist[
  @item{@term[(--> (in-hole E (ap (λ x t_x e_11) v_12)) (in-hole E (substitute e_11 x v_12)))].
         By the replacement lemma, we know that
         @term[(types* (ap (λ x t_x e_11) v_12) t_1)].
         This only types if @term[(types* (λ x t_x e_11) (-> t_x t_1))]
         and @term[(types* v_12 t_x)]. The former is only the case
         if @term[(types (extend • x t_x) e_11 t_1)].
         Then by the substitution lemma,
         @term[(types* (substitute e_11 x v_12) t_1)], and by replacement,
         @term[(types* (in-hole E (substitute e_11 x v_12)) t)].}
]

QED.

@lemma[#:name "Canonical forms"]

If @term[(types* v t)] then:

@itemlist[
 @item{If @term[t] is @term[nat], then @term[v] is either @term[z] or
       or @term[(s v_1)] for some @term[v_1].}
 @item{If @term[t] is @term[(-> t_1 t_2)], then @term[v] is some lambda
 abstraction @term[(λ x t_1 e_1)].}
]

@proof[] By induction on the structure of the typing derivation. Only three
rules form values, and those three rules correspond to the conditions of the
lemma.

@lemma[#:name "Progress"]{If @term[(types* e_1 t)] then either @term[e_1] is a
 value or @term[(--> e_1 e_2)] for some @term[e_2].}

@proof[] By induction on the structure of the typing derivation, considering
the terms:

@itemlist[
 @item{@term[x]: Vacuous, open terms don't type.}
 @item{@term[z]: A value.}
 @item{@term[(s e)]: By induction, @term[e] steps or is a value of type
  @term[nat]. If the former then the whole term steps; if the latter then
  the whole term is a value.}
 @item{@term[(ap e_11 e_12)]: By induction, each subterm steps or is a value.
        If the first subterm steps, then the whole term steps.
        If the first subterm is a value and the second steps, then the whole
        thing steps. If both are values, then by inversion of the @rulename[app]
        rule, @term[e_11] has a function type, and by the canonical forms lemma,
        that means it is a lambda abstraction @term[(λ x e)].
        Then the whole term steps to @term[(substitute e x e_12)].}
 @item{@term[(λ x t_1 e)]: A value.}
]

@theorem[#:name "Safety"]{1) If @term[(types* e_1 t)] and @term[(--> e_1 e_2)]
 then @term[(types* e_2 t)]. 2) If @term[(types* e_1 t)] then either
 @term[e_1] is a value or @term[(--> e_1 e_2)] for some @term[e_2].}

@exercise{Extend @stlc with a product type @term[(* t_1 t_2)].
 You will need a form for
 constructing products and projections for getting the components out.}

@exercise{Extend @stlc with a sum type @term[(+ t_1 t_2)]. You will need two
 injection forms @term[(inl e)] and @term[(inr e)] to create sums, and one
 case analysis form to eliminate them,
 @term[(match e [x e_l] [y e_r])].} The case analysis form takes a step once
 @term[e] reduces to a sum value:
 @term[(--> (match (inl v) [x e_l] [y e_r]) (substitute e_l x v))],
 and similarly for @term[(inr v)].}

@section[#:tag "stlc-an-extension"]{An Extension}

As it stands, we can’t do much with natural numbers. We can add a limited,
terminating form of recursion, as follows. We extend the syntax of terms and
evaluation contexts as follows:
@;
@render-nonterminals[r:stlc/rec e E]
@;
The new form is the recursor, which works as follows. First, it evaluates
@term[e] to a value, which must be a natural number. If that number is zero,
then it evaluates @term[e_z]. Otherwise, if that term is a successor
@term[(s v)], it recurs on @term[v], binding the recursive result to
@term[y_rec] and the predecessor @term[v] to @term[x_pre] in @term[e_s].

There are no new types. We extend the reduction relation with two cases
representing the just-described dynamics:
@;
@render-reduction-rules[r:->val/rec rec-zero rec-succ]

There is one rule for typing the new form:
@;
@render-judgment-rules[r:types/rec rec]

@exercise{Extend the safety theorem for the recursor.}

@exercise{The recursor is currently call-by-name. To make it call-by-value
          requires introducing an additional form. @term[let] will do. Show
          how to add @term[let] to @stlc and how that can be used to make the
          recursor call-by-value.}

@section[#:tag "stlc-normalization"]{Strong Normalization}

Define @term[(⇓ e)] to mean that @term[e] reduces to some value @term[v]:
@term[(-->* e v)].

We wish to show that all terms that have a type reduce to a value.
It is insufficient
to do induction on typing derivations. What we end up needing is a relation
between terms and types, defined by induction on types,
of the form @term[(SN t e)], as follows:

@itemlist[
  @item{@term[(SN nat e)] iff @term[(types* e nat)] and @term[(⇓ e)].}
  @item{@term[(SN (-> t_1 t_2) e)] iff @term[(types* e (-> t_1 t_2))]
         and @term[(⇓ e)] and for all @term[e_1] such that @term[(SN t_1 e_1)],
         @term[(SN t_2 (ap e e_1))].}
]

@lemma[#:name "SN preserved by reduction"]

Suppose that @term[(types* e_1 t)] and @term[(--> e_1 e_2)]. Then:

@itemlist[
 @item{@term[(SN t e_2)] implies @term[(SN t e_1)].}
 @item{@term[(SN t e_1)] implies @term[(SN t e_2)].}
]

@proof[] By induction on @term[t]:

@itemlist[
 @item{@term[nat]: If @term[e_2] converges then @term[e_1] converges
        by the same sequence. Since it has types @term[t], we have
        @term[(SN nat e_1)]

        If @term[e_1] converges then it does so via
        @term[e_2], so @term[e_2] converges as well, and by preservation it has
        the same type, so @term[(SN nat e_2)].}
 @item{@term[(-> t_1 t_2)]: If @term[(SN (-> t_1 t_2) e_2)] then we know that
        @term[e_2] converges and when applied to a good term, that converges
        too. We need to show that @term[e_1] does that same, that is,
        that @term[(SN t_1 e_arb)] implies that @term[(SN t_2 (ap e_1 e_arb))]
        for arbitrary term @term[e_arb]. We know that
        @term[(SN t_2 (ap e_2 e_arb))]. Since @term[(--> e_1 e_2)], we know that
        @term[(--> (ap e_1 e_arb) (ap e_2 e_arb))]. Since @term[t_2] is a
        subexpression of @term[(-> t_1 t_2)], we can apply the induction
        hypothesis at that type, yielding @term[(SN t_2 (ap e_1 e_arb))]
        as desired.

        If @term[(SN (-> t_1 t_2) e_1)] then we know that
        @term[e_1] converges and when applied to a good term, that converges
        too. We need to know that @term[e_2] does the same, that is, that
        @term[(SN t_1 e_arb)] implies that @term[(SN t_2 (ap e_2 e_arb))]
        for arbitrary term @term[e_arb]. We know that
        @term[(SN t_2 (ap e_1 e_arb))]. Since @term[(--> e_1 e_2)], we know that
        @term[(--> (ap e_1 e_arb) (ap e_2 e_arb))]. Then by induction,
        @term[(SN t_2 (ap e_2 e_arb))].}
]

QED.

Next, we define substitutions, and what it means for a substitution to
satisfy a typing environment:

@render-nonterminals[r:stlc γ]

@render-judgment-rules[r:satisfies nil cons]

@lemma[#:name "Mass substitution"]{If @term[(types Γ e t)]
 and @term[(satisfies γ Γ)] then
 @term[(types • (γ e) t)].}

@proof[] By induction on the length of @term[γ]. If empty, then @term[Γ] is
empty, and the substitution has no effect. Otherwise, @term[γ] =
@term[(extend γ_1 x v_x)], where @term[Γ] = @term[(extend Γ_1 x t_x)]
and @term[(satisfies γ_1 Γ_1)] and @term[(NT t_x v_x)]. Then by the
substitution lemma, @term[(types Γ_1 (substitute e x v_x) t)].
Then by induction, @term[(types • (γ_1 (substitute e x v_x)) t)].
But that is @term[(γ e)].

@lemma[#:name "Every typed term is good"]{If @term[(types Γ e t)]
 and @term[(satisfies γ Γ)] then @term[(NT t (γ e))].}

@proof[] By induction on the typing derivation:

@itemlist[
 @item{@term[(types Γ x (lookup Γ x))]: Appling @term[γ] to @term[x]
        gets us a @term[v] such that @term[(NT (lookup Γ x) v)].}
 @item{@term[(types Γ z nat)]: Since @term[z] = @term[(γ z)], and
        @term[(types • z nat)] and @term[(⇓ z)], we have that
        @term[(NT nat z)].}
 @item{@term[(types Γ (s e_1) nat)]: By inversion, we know that
        @term[(types Γ e_1 nat)]. Then by induction, we have that
        @term[(NT nat (γ e_1))]. By the definition of NT for @term[nat],
        we have that @term[(γ e_1)] types in the empty context and reduces
        to a natural number. Then @term[(γ (s e_1))] does as well.}
 @item{@term[(types Γ (ap e_1 e_2) t)]: By inversion, we know that
        @term[(types Γ e_1 (-> t_2 t))] and
        @term[(types Γ e_2 t_2)]. By induction, we know that
        @term[(SN (-> t_2 t) e_1)] and @term[(SN t_2 e_2)].
        The former means that for any @term[e_arb] such that
        @term[(SN t_2 e_arb)], we have @term[(SN t (ap e_1 e_arb))].
        Let @term[e_arb] be @term[e_2]. Then @term[(SN t (ap e_1 e_2))].}
 @item{@term[(types Γ (λ x t_1 e_2) (-> t_1 t_2))]:
        Without loss of generality, let @term[x] be fresh for @term[γ].
        So then that term equals @term[(λ x t_1 (γ e_1))].
        We need to show that @term[(SN (-> t_1 t_2) (λ x t_1 (γ e_2)))].
        To show this, we need to show three things:
  @itemlist[
    @item{To show @term[(types • (λ x t_1 (γ e_2)) (-> t_1 t_2))].
          It suffices to show that
          @term[(types Γ (λ x t_1 e_2) (-> t_1 t_2))] for some @term[Γ]
          such that @term[(satisfies γ Γ)], by the mass substitution lemma.
          That is what we have.}
    @item{To show @term[(⇓ (λ x t_1 (γ e_2)))]. This is clear, because it is a
          value.}
    @item{To show that for any @term[e_1] such that @term[(SN t_1 e_1)],
          @term[(SN t_2 (ap (λ x t_1 (γ e_2)) e_1))]. By the definition of
          SN, we know that @term[(-->* e_1 v_1)] for some value @term[v_1].
          Then by the lemma that SN is preserved by reduction, we know that
          @term[(SN t_1 v_1)]. So then we can say that
          @term[(satisfies (extend γ x v_1) (extend Γ x t_1))].
          Then we can take a step
          @term[(--> (ap (λ x t_1 (γ e_2)) v_1) ((extend γ x v_1) e_2))].
          By preservation, @term[(types • ((extend γ x v_1) e_2) t_2)].
          So we can apply the induction hypothesis to conclude that
          @term[(SN t_2 ((extend γ x v_1) e_2))]. Then by reduction preserving
          SN, we can conclude that @term[(SN t_2 (ap (λ x t_1 (γ e_2)) e_1))].}
   ]}
]

QED.

Strong normalization follows as a corollary.

@exercise{Show that @stlc with the recursor still enjoys strong
 normalization.}


