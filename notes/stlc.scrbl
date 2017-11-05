#lang scribble/base

@(require (prefix-in r: "redex/stlc.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:stlc)
@define[stlc]{@langname[λ-st]}

@title{The simply-typed lambda calculus @stlc}

@section[#:tag "stlc-syntax"]{Syntax}

The @stlc language has types @term[t] and terms @term[e] defined as follows:
@;
@render-nonterminals[r:stlc t e x y]
@;
Types include the natural numbers @term[nat] and function types
@term[(-> t_1 t_2)]. Terms include variables, Peano naturals (@term[z] for
zero and @term[s] for successor), lambda abstractions, and applications.

@section[#:tag "stlc-dynamics"]{Dynamic semantics}

To define the dynamic semantics of @stlc, we give syntax for values and
evaluation contexts:
@;
@render-nonterminals[r:stlc v E]
@;
Values include natural numbers and lambda abstractions. We evaluate under
@term[s] and we evaluate both the operator and operand in an application.

Then the reduction relation consists of one rule:
@;
@render-reduction-rules[r:->val β-val]

The dynamic semantics of @stlc is given by the evaluation function @emph{eval}:
@;
@centered[
@tabular[
 #:sep @hspace[1]
 #:column-properties '(left left)          
 (list (list @list{eval(@term[e]) = @term[v]}
             @list{if @term[(-->* e v)]}))
]
]
@;
As defined, @emph{eval} could be partial, but we will prove it total on
well typed terms, first by proving that well typed terms don’t go wrong,
and then by proving that well typed terms don’t diverge.

@section[#:tag "stlc-statics"]{Static semantics}

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

@exercise{Extend @stlc with a product type @term[(* t_1 t_2)].
 You will need a form for
 constructing products and projections for getting the components out. Add the
 necessary reduction and typing rules.}

@exercise{Extend @stlc with a sum type @term[(+ t_1 t_2)]. You will need two
 injection forms @term[(inl e)] and @term[(inr e)] to create sums, and one
 case analysis form to eliminate them,
 @term[(match e [x e_l] [y e_r])]. The case analysis form takes a step once
 @term[e] reduces to a sum value:
 @term[(--> (match (inl v) [x e_l] [y e_r]) (substitute e_l x v))],
 and similarly for @term[(inr v)]. Add the necessary reduction and typing
 rules.}

@subsection[#:tag "stlc-type-safety"]{Type safety}

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
        @term[(types Γ (substitute (s e) x e_1) nat)].}
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

@exercise{Extend the type safety theorem to cover product and/or sum types.}

@section[#:tag "stlc-an-extension"]{An extension}

As it stands, we can’t do much with natural numbers. Inspired by Gödel’s
system T, we add a limited, terminating form of recursion on natural numbers.
We extend the syntax of terms and evaluation contexts as follows:
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
@render-judgment-rules[r:types/alt rec]

Here is predecessor expressed using the recursor:
@;
@centered{
 pred = @term[(λ n nat (rec n [z] [x_pre y_rec x_pre]))]
}
@;
For zero it returns zero, and for any other number it returns the predecessor,
ignoring the recursive result.

And here is addition expressed using the recursor:
@;
@centered{
 add = @term[(λ n nat (λ m nat (rec n [m] [x_pre y_rec (s y_rec)])))]
}

@exercise{Implement multiplication using the recursor.}

@exercise{Implement factorial using the recursor.}

@exercise{Implement a function that divides a natural number by two (rounding
 down.}

@exercise{Extend the type safety theorem for the recursor.}

@exercise{The recursor is currently call-by-name, in the sense that it
 substitutes the whole recursive expression of
 @term[(rec v [e_z] [x_pre y_rec e_s])] for @term[y_rec] in the non-zero case.
 The call-by-value form would compute the value of that subterm first and
 then subtitute the value, but making it call-by-value
 requires introducing an additional form. @term[let] will do.
 (Why can’t we just use λ?) Show
 how to add @term[let] to @stlc and how that can be used to make the
 recursor call-by-value.}

@section[#:tag "stlc-normalization"]{Normalization}

A normal form is a form that doesn’t reduce any further, which for our purposes
(since we have eliminated stuck states) is a value. A term @term[e]
normalizes, written @term[(⇓ e)] if it reduces to a normal form, that is,
a value.

Historically, when working with lambda calculi that allow free conversion
(that is, redexes can by identified anywhere in a term, without a notion of
evaluation contexts)
authors have distinguished weak from strong normalization. A term weakly
normalizes if it has some reduction sequence reaching a normal form; a term
strongly normalizes if every of its reduction sequences reaches a normal form.
However, we’ve defined our language to be deterministic, which causes weak and
strong normalization to coincide.

We wish to show that all terms that have a type reduce to a value.
It is insufficient to do induction on typing derivations.
(Shall we try it?)  What we end up needing is a (unary)
relation on terms, indexed by types, and defined by induction on types,
of the form @term[(SN t e)], as follows:

@itemlist[
  @item{@term[(SN nat e)] iff @term[(types* e nat)] and @term[(⇓ e)].}
  @item{@term[(SN (-> t_1 t_2) e)] iff @term[(types* e (-> t_1 t_2))]
         and @term[(⇓ e)] and for all @term[e_1] such that @term[(SN t_1 e_1)],
         @term[(SN t_2 (ap e e_1))].}
]

@exercise{How would we extend @term[SN] for product and/or sum types?}

@lemma[#:name "SN preserved by conversion"]

Suppose that @term[(types* e_1 t)] and @term[(--> e_1 e_2)]. Then:

@itemlist[
 @item{@term[(SN t e_2)] implies @term[(SN t e_1)].}
 @item{@term[(SN t e_1)] implies @term[(SN t e_2)].}
]

@proof[] By induction on @term[t]:

@itemlist[
 @item{@term[nat]: If @term[e_2] normalizes then @term[e_1] normalizes
        by the same sequence because @term[e_1] takes a step to @term[e_2],
        which then normalizes. Since it has type @term[t], we have
        @term[(SN nat e_1)]

        If @term[e_1] normalizes then it does so via
        @term[e_2], so @term[e_2] normalizes as well, and by preservation it has
        the same type, so @term[(SN nat e_2)].}
 @item{@term[(-> t_1 t_2)]: If @term[(SN (-> t_1 t_2) e_2)] then we know that
        @term[e_2] normalizes and when applied to a good term, that normalizes
        too. We need to show that @term[e_1] does that same, that is,
        that @term[(SN t_1 e_arb)] implies that @term[(SN t_2 (ap e_1 e_arb))]
        for arbitrary term @term[e_arb]. We know that
        @term[(SN t_2 (ap e_2 e_arb))]. Since @term[(--> e_1 e_2)], we know that
        @term[(--> (ap e_1 e_arb) (ap e_2 e_arb))]. Since @term[t_2] is a
        subexpression of @term[(-> t_1 t_2)], we can apply the induction
        hypothesis at that type, yielding @term[(SN t_2 (ap e_1 e_arb))]
        as desired.

        If @term[(SN (-> t_1 t_2) e_1)] then we know that
        @term[e_1] normalizes and when applied to a good term, that normalizes
        too. We need to know that @term[e_2] does the same, that is, that
        @term[(SN t_1 e_arb)] implies that @term[(SN t_2 (ap e_2 e_arb))]
        for arbitrary term @term[e_arb]. We know that
        @term[(SN t_2 (ap e_1 e_arb))]. Since @term[(--> e_1 e_2)], we know that
        @term[(--> (ap e_1 e_arb) (ap e_2 e_arb))]. Then by induction,
        @term[(SN t_2 (ap e_2 e_arb))].}
]

QED.

Next, we define substitutions, and what it means for a substitution to
satisfy a typing environment. A substitution associates some variables
with values to substitute them:
@;
@render-nonterminals[r:stlc γ]
@;
To apply a substitution to a term, written @term[(apply-substitution e γ)],
is to substitute in the term the values of the substitution for their
variables.

A substitution satisfies a typing environment if they have the same domains
(sets of variables) and every value in the
substitution not only  has the type given for the corresponding variable in the
type environment, but is SN for that type:
@;
@render-judgment-rules[r:satisfies nil cons]

Note that if a substitution satisfies a type environment, this means that
it contains values that typed in the empty type environment, meaning they are
closed. Thus, the order of substitution doesn’t matter, as no variable in
the substitution will interfere with any other.

Now we can prove a lemma that if we apply a substitution to a term that types
in an environment consistent with the substitution, then the substituted
term types in the empty environment:

@lemma[#:name "Mass substitution"]{If @term[(types Γ e t)]
 and @term[(satisfies γ Γ)] then
 @term[(types • (apply-substitution e γ) t)].}

@proof[] By induction on the length of @term[γ]. If empty, then @term[Γ] is
empty, and the substitution has no effect. Otherwise, @term[γ] =
@term[(extend-substitution γ_1 x v_x)],
where @term[Γ] = @term[(extend Γ_1 x t_x)]
and @term[(satisfies γ_1 Γ_1)] and @term[(SN t_x v_x)]. Then by the
substitution lemma, @term[(types Γ_1 (substitute e x v_x) t)].
Then by induction,
@term[(types • (apply-substitution (substitute e x v_x) γ_1) t)].
But that is @term[(apply-substitution e γ)].

@lemma[#:name "Every typed term is good"]{If @term[(types Γ e t)]
 and @term[(satisfies γ Γ)] then @term[(SN t (apply-substitution e γ))].}

@proof[] By induction on the typing derivation:

@itemlist[
 @item{@term[(types Γ x (lookup Γ x))]: Appling @term[γ] to @term[x]
        gets us a @term[v] such that @term[(SN (lookup Γ x) v)].}
 @item{@term[(types Γ z nat)]: Since @term[z] =
  @term[(apply-substitution z γ)], and
        @term[(types • z nat)] and @term[(⇓ z)], we have that
        @term[(SN nat z)].}
 @item{@term[(types Γ (s e_1) nat)]: By inversion, we know that
        @term[(types Γ e_1 nat)]. Then by induction, we have that
        @term[(SN nat (apply-substitution e_1 γ))].
        By the definition of NT for @term[nat],
        we have that @term[(apply-substitution e_1 γ)]
        types in the empty context and reduces
        to a natural number. Then @term[(apply-substitution (s e_1) γ)]
        does as well.}
 @item{@term[(types Γ (ap e_1 e_2) t)]: By inversion, we know that
        @term[(types Γ e_1 (-> t_2 t))] and
        @term[(types Γ e_2 t_2)]. By induction, we know that
        @term[(SN (-> t_2 t) e_1)] and @term[(SN t_2 e_2)].
        The former means that for any @term[e_arb] such that
        @term[(SN t_2 e_arb)], we have @term[(SN t (ap e_1 e_arb))].
        Let @term[e_arb] be @term[e_2]. Then @term[(SN t (ap e_1 e_2))].}
 @item{@term[(types Γ (λ x t_1 e_2) (-> t_1 t_2))]:
        Without loss of generality, let @term[x] be fresh for @term[γ].
        So then that term equals @term[(λ x t_1 (apply-substitution e_1 γ))].
        We need to show that
        @term[(SN (-> t_1 t_2) (λ x t_1 (apply-substitution e_2 γ)))].
        To show this, we need to show three things:
  @itemlist[
    @item{To show
          @term[(types • (λ x t_1 (apply-substitution e_2 γ)) (-> t_1 t_2))].
          It suffices to show that
          @term[(types Γ (λ x t_1 e_2) (-> t_1 t_2))] for some @term[Γ]
          such that @term[(satisfies γ Γ)], by the mass substitution lemma.
          That is what we have.}
    @item{To show @term[(⇓ (λ x t_1 (apply-substitution e_2 γ)))].
          This is clear, because it is a value.}
    @item{To show that for any @term[e_1] such that @term[(SN t_1 e_1)],
          @term[(SN t_2 (ap (λ x t_1 (apply-substitution e_2 γ)) e_1))]. By the definition of
          SN, we know that @term[(-->* e_1 v_1)] for some value @term[v_1].
          Then we can take an additional step,
          @term[(--> (ap (λ x t_1 (apply-substitution e_2 γ)) v_1) (substitute (apply-substitution e_2 γ) x v_1))].
          Because SN is preserved by backward conversion, it suffices to show
          that this term is SN for @term[t_2].
          
          By the lemma that SN is preserved by forward conversion, we know that
          @term[(SN t_1 v_1)]. So then we can say that
          @term[(satisfies (extend-substitution γ x v_1) (extend Γ x t_1))].
          Now consider inverting the judgment that
          @term[(types Γ (λ x t_1 e_2) (-> t_1 t_2))]. From this, we know that
          @term[(types (extend Γ x t_1) e_2 t_2)]. Then applying the induction
          hypothesis, we have that
          @term[(SN t_2 (apply-substitution e_2 (extend-substitution γ x v_1)))].
          This is what we sought to show.}
   ]}
]

QED.

Strong normalization follows as a corollary.

@exercise{Extend the normalization proof to cover products and/or sums.}

@exercise{Show that @stlc with the recursor still enjoys normalization.}

@section[#:tag "stlc-fix"]{Adding nontermination}

We can add unrestricted recursion to @stlc by adding a fixed-point operator.
The new expression form is @term[(fix e)]:
@;
@render-nonterminals[r:stlc/fix e]

What @term[fix] does at run time is apply its argument, which must
be a function, to the @term[fix] of itself, thus implementing recursion:
@;
@render-reduction-rules[r:->val/fix fix]

To type @term[fix], we type its argument, which must be a function from
the desired type to itself:
@;
@render-judgment-rules[r:types/alt fix]

@exercise{Extend type safety for @term[fix].}

@exercise{Where does the normalization proof break down if we add @term[fix]?}