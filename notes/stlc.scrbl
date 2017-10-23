#lang scribble/base

@(require (prefix-in r: "redex/stlc.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:stlc)
@define[stlc]{@langname[λ-st]}

@title{The Simply-Typed Lambda Calculus @stlc}

@section{Syntax}

The @stlc language has types @term[t] and terms @term[e] defined as follows:

@render-nonterminals[r:stlc t e]

@section{Dynamic Semantics}

To define the dynamic semantics of @stlc, we give syntax for values and
evaluation contexts:

@render-nonterminals[r:stlc v E].

Then the reduction relation consists of one rule:

@render-reduction-rules[r:->val β-val]

@section{Static Semantics}

To type @stlc, we define typing contexts mapping variables to types:

@render-nonterminals[r:stlc Γ]

Then the rules are as follows. There are two constructors for the
naturals, and they type as such:
@;
@render-judgment-rules[r:types zero succ]

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

@subsection{Type Safety}

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
         if @term[(types ([x t_x]) e_11 t_1)].
         Then by the substitution lemma,
         @term[(types* (substitute e_11 x v_12) t_1)], and by replacement,
         @term[(types* (in-hole E (substitute e_11 x v_12)) t)].}
]

QED.

@lemma[#:name "Canonical forms"]

If @term[(types* v t)] then:

@itemlist[
 @item{If @term[t] is @term[nat], then @term[v] is either @term[nil] or
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
        Then the whole term steps to @term[(substituted e x e_12)].}
 @item{@term[(λ x t_1 e)]: A value.}
]

@theorem[#:name "Safety"]{1) If @term[(types* e_1 t)] and @term[(--> e_1 e_2)]
 then @term[(types* e_2 t)]. 2) If @term[(types* e_1 t)] then either
 @term[e_1] is a value or @term[(--> e_1 e_2)] for some @term[e_2].}

@section{An Extension}

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

