#lang scribble/base

@(require (prefix-in r: "redex/let-nl.rkt")
          (prefix-in r: "redex/let-nl-t.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:let-nl)
@define[let-nl]{@langname[let-nl]}

@title{The @let-nl Language}

@section{Syntax}

The @let-nl language has expressions @term[e] defined as follows:

@centered[
 (with-rewriters @render-language[r:let-nl])
]

There are two kinds of literal expressions, integers @term[n] and the empty
list @term[nil]. Additionally, we build longer lists with @term[(cons e_1 e_2)],
which is our traditional cons that creates a linked list node with first and
rest. We have two elimination forms for integers,
@term[(+ e_1 e_2)] and @term[(* e_1 e_2)].
Additionally, we have elimination forms for lists, @term[(car e)] and
@term[(cdr e)]. Finally, we have variables @term[x], and we have a form of
sharing in @term[(let x e_1 e_2)], which binds @term[x] to the value of
@term[e_1] in @term[e_2].

@section{Dynamic Semantics}

We might have a decent guess as to what this language means, but to be precise,
we will define its dynamic semantics using a rewriting system.  The reduction
relation describes a single computation step, and has a case for each kind of
basic computation step that our language performs. For example, here is how we
perform addition:
@;
@render-reduction-rules[r:->val plus]
@;
The @rulename[plus] rule says that to reduce an addition
expression where both parameters are already reduced to numbers, we
add the numbers in the metalanguage. The @term[E] portion of each term
is the evaluation context, which means that addition can be performed
not just on whole terms, but within terms according to a grammar given
below.

The multiplication is similar, also allowing multiplication within any
evaluation context:
@;
@render-reduction-rules[r:->val times]

We have two rules for getting the first and rest of a list:
@;
@render-reduction-rules[r:->val car cdr]
@;
These say that if we have a cons (pair) of values @term[(cons v_1 v_2)] then
@term[car] extracts the first value @term[v_1] and @term[cdr] extracts the
second value @term[v_2].

There are also two rules that say what @term[car] and @term[cdr] do when given
@term[nil], the empty list:
@;
@render-reduction-rules[r:->val car-nil cdr-nil]
@;
These are errors! When applied to the empty list, @term[car] and @term[cdr]
discard their context and reduce to a special configuration @term[WRONG].

Finally, the rule for @term[let] involves substituting the value for the
variable in the body:
@;
@render-reduction-rules[r:->val let]

In order to describe where evaluation can happen when when it is finished, we
extend our syntax with values @term[v], evaluation contexts @term[E], and
configurations @term[C]:

@centered{
 @render-language[r:let-nl/eval]
}

We define values—final results—to include numbers @term[n], the empty list
@term[nil], and pairs of values @term[(cons v_1 v_2)].

Evaluation context @term[E] give a grammar for where evaluation can take place.
For example, suppose we want to reduce the term @term[(* (+ 1 2) (+ 3 4))].
We need to decompose that term into an evaluation context and a redex, so that
they match one of the reduction rules above. We can do that: the evaluation
context is @term[(* hole (+ 3 4))], which matches the grammar of @term[e], and
the redex in the hole is thus @term[(+ 1 2)]. This decomposition matches rule
@rulename[plus], which reduces it to @term[(* 3 (+ 3 4))]. Then to perform
another reduction, we decompose again, into evaluation context @term[(* 3 hole)]
and redex @term[(+ 3 4)]. That reduces to @term[7] plugged back into the
evaluation context, for @term[(* 3 7)]. Then to perform one more reduction step,
we decompose into the evaluation context @term[hole] and the redex
@term[(* 3 7)], which reduces to @term[21].

Configurations specify what we actually reduce over: expressions @term[e] or
the special error token @term[WRONG].

@exercise{Extend the language with Booleans. Besides Boolean literals, what
          do you think are essential operations? Extend the dynamic semantics
          with the necessary reduction rule(s) and evaluation context(s).}

@subsection{Errors}

@let-nl has two explicit error cases, @term[(car nil)] and @term[(cdr nil)],
which both reduce to @term[WRONG]. Are there any other ways @let-nl programs
can go wrong?

Indeed, there are terms that do not reduce. In particular:

@itemlist[
  @item{@term[(car n)] and @term[(cdr n)], where @term[n] is an integer.}
  @item{@term[(+ v_1 v_2)] or @term[(* v_1 v_2)] where @term[v_1] or @term[v_2]
         is not an integer.}
  @item{Any open term, that is, a term with a variable that is not bound by
            @term[let].}
]

Currently, our model gets @italic{stuck} on these erroneous kinds of terms.
This might correspond to a real language executing an invalid instruction
or in some other kind of undefined behavior. There are two main ways we could
solve the problem. First, we could add transition rules that detect all bad
states and transition them to @term[WRONG], thus flagging them as errors.
Or second, we could impose a type system, which rules out programs with
some kinds of errors. We can then prove that no programs admitted by the
type system get stuck.

@section{Static Semantics}

With a type system, we assign types to (some) terms to classify them by
what kind of value they compute. In our first, simple type system, we
will have only two types of values:
@;
@render-nonterminals[r:let-nl/t t]
@;
To keep things simple, we will limit @term[list] to be lists of integers.

We then define a relation that assigns types to terms. For example, integer
literals always have type @term[int]:
@;
@render-judgment-rules[r:types* int]

Similarly, the literal empty list has type @term[list]:
@;
@render-judgment-rules[r:types* nil]

To type check an addition or multiplication, we check that the operands are both
integers, and then the whole thing is an integer:
@;
@render-judgment-rules[r:types* plus times]

To type check a @term[cons], we require that the first operand be an integer
and the second be a list, and then the whole thing is a list:
@;
@render-judgment-rules[r:types* cons]

To type check @term[car] and @term[cdr], we require that the operand be a list;
the result for @term[car] is an integer, and the result for @term[cdr] is
another list:
@;
@render-judgment-rules[r:types* car cdr]

But when we come to check a variable @term[x], we get stuck. What’s the type of
a variable? To type check variables, we introduce type environments, which keep
track of the type of each @term[let]-bound variable:
@;
@render-nonterminals[r:let-nl/t Γ]

We then retrofit all our rules to carry the environment @term[Γ] through. For
example, the rule for @term[car] becomes
@;
@render-judgment-rules[r:types car]
@;
and similarly for the other rules we’ve seen so far.

Then we can write the rules for variables and for @term[let]. To type check a
variable, look it up in the environment:
@;
@render-judgment-rules[r:types var]
@;
If it isn’t found, then the term is open and does not type.

Finally, to type check @term[(let x e_1 e_2)], we first type check
@term[e_1], yielding some type @term[t_1]. We then type check
@term[e_2] with an environment extended with @term[x] bound to
@term[t_1]. The resulting type, @term[t_2], is the type of the whole
expression:
@;
@render-judgment-rules[r:types let]

@exercise{Extend the type system to your language with Booleans.}

@exercise[#:name "Generic lists"]{
 Modify the type system as follows: instead of a single type
 @term[list] for lists of @term[int]s, allow @term[(list int)],
 @term[(list (list int))], @term[(list (list (list int)))] and so on.
 How do you have to change the syntax of @term[t]? The typing rules?}

@subsection{Type Safety}

The goal of our type system is to prevent undetected errors—that is,
stuck terms—in our programs. To show that it does this, we will prove
@italic{type safety}: if a term @term[e] has a type @term[t], then
one of:
@;
@itemlist[
  @item{It will reduce in some number of steps to a value @term[v] that also
        has type @term[t].}
  @item{It will reduce in some number of steps to @term[WRONG].}
  @item{It will reduce forever.}
]
@;
The last case cannot happen with this language, but it will be possible
with languages we study in the future.

It is conventional to prove this theorem in terms of two lemmas,
progress and preservation:
@;
@itemlist[
  @item{Preservation: if @term[e_1] has type @term[t] and reduces in
        one step to @term[e_2], then @term[e_2] also has type @term[t].}
  @item{Progress: if @term[e] has a type @term[t], then either @term[e]
        reduces or @term[e] is a value.}
]

@subsubsection{Preservation}

We want to prove that if a term has a type and takes a step, the resulting
term also has a type. We can do this be considering the cases of the
reduction relation and showing that each preserves the type. Alas, each rule
involves evaluation contexts @term[E] in the way of the action. Consequently,
we’ll have to prove a lemma about evaluation contexts.

@lemma[#:name "Replacement"]{If
@term[(types () (in-hole E e_1) t)], then there exists some type
@term[t_e] such that
@term[(types () e_1 t_e)]. Furthermore, for any other term @term[e_2]
such that @term[(types () e_2 t_e)], it is the case that
@term[(types () (in-hole E e_2) t)].}

@proof[] By induction on the structure of @term[E]:

@itemlist[
  @item{If @term[E] is @term[hole], then @term[e] = @term[(in-hole E e_1)],
       so @term[t_e] must be @term[t]. Then since @term[(types () e_2 t_e)],
       we have that @term[(types () (in-hole E e_2) t_e)].}
  @item{If @term[(cons E_1 e_22)], then the only typing rule that applies
           is @rulename[cons], which means that @term[t] must be @term[list].
           Furthermore, by inversion of that rule it must be the case that
           @term[(types () (in-hole E_1 e_1) int)]
           and @term[(types () e_22 list)]. By the induction
           hypothesis on the former, @term[e_1] has some type
           @term[t_e], and furthermore, for any term @term[e_2] that also
           has type @term[t_e], we have that
           @term[(types () (in-hole E_1 e_2) int)]. Then by applying rule
           @rulename[list], we have that
           @term[(types () (in-hole (cons E_1 e_22) e_2) list)].}
  @item{If @term[(cons e_11 E_2)], then as in the previous case, the only typing
           rule that applies is @rulename[cons], which means that @term[t]
           must be @term[list]. It also means that
           @term[(in-hole E_2 e_1)] must have type @term[list]
           and @term[e_11] must have type @term[int]. Then by IH on the former,
           @term[e_1] has a type @term[t_e], and furthermore, for any @term[e_2]
           having type @term[t_e], @term[(types () (in-hole E_2 e_2) t_e)].
           Then by reapplying rule @rulename[cons], we have that
           @term[(types () (in-hole E e_2) list)].}
  @item{If @term[(+ E_1 e_22)], then the only typing rule that applies is
           @rulename[plus], which means that @term[t] is @term[int]. It also
           requires that @term[(in-hole E_1 e_1)] and
           @term[e_22] both have type @term[int]. Then apply IH to the former,
           yielding that @term[e_1] has some type @term[t_e]. Furthermore, by
           the IH, for any other @term[e_2] having type @term[t_e], we have that
           @term[(types () (in-hole E_1 e_2) t_e)]. Then reapplying rule
           @rulename[plus], we have that @term[(types () (in-hole E e_2) int)].}
  @item{If @term[(+ v_1 E_2)] or @term[(* E_1 e_2)] or @term[(* v_1 E_2)],
           as in the previous case, m.m.}
  @item{If @term[(car E_1)] (or @term[(cdr E_1)]) then the only typing rule
           that applies is @rulename[car] (resp. @rulename[cdr]), which means
           that @term[t] is @term[int] (resp. @term[list]).
           Furthermore, rule @rulename[car] (resp. @rulename[cdr])
           requires that @term[(in-hole E_1 e_1)] must have type @term[list].
           Then apply IH to get that @term[(types () (in-hole E_1 e_2) list)]
           as well. Then @term[(types () (in-hole E e_2) list)] as well.
           Then apply rule @rulename[car] (resp. @rulename[cdr]) to get that
           @term[(in-hole E e_2)] has type @term[int] (resp. @term[list]).}
  @item{If @term[(let x E_1 e_22)], then the only rule that applies is
           @rulename[let]. By that rule, @term[(in-hole E_1 e_1)] must have
           some type @term[t_1], and @term[(types ([x t_1]) e_22 t)].
           Then by the IH on the former, @term[(types () e_1 t_e)] for some
           @term[t_e]. Furthermore, for any other @term[e_2] having type
           @term[t_e], the IH tells us that
           @term[(types () (in-hole E_1 e_2) t_1)] as
           well. Then we can reapply rule @rulename[let] to get
           @term[(types () (in-hole (let x E_1 e_22) e_2) t)].}
]

QED.

There’s one more standard lemma we need before we can prove preservation:

@lemma[#:name "Substitution"]{If @term[(extend Γ x t_x)] ⊢ @term[e] :
@term[t] and @term[Γ] ⊢ @term[v] : @term[t_x] then
@term[Γ] ⊢ @term[(substitute e x v)] : @term[t].}

@proof[]. By induction on the typing deriviation for @term[e]; by cases
on the conclusion:

@itemlist[
 @item{@term[(types (extend Γ x t_x) n int)]: Then @term[(substitute n x v)] is
        @term[n], and @term[(types Γ n int)].}
 @item{@term[(types (extend Γ x t_x) nil list)]: Then
        @term[(substitute nil x v)]
        is @term[nil], and @term[(types Γ nil list)].}
 @item{@term[(types (extend Γ x t_x) (cons e_1 e_2) list)]: Then we know that
        @term[(types (extend Γ x t_x) e_1 int)] and
        @term[(types (extend Γ x t_x) e_2 list)].
        Then by the induction hypothesis,
        @term[(types Γ (substitute e_1 x v) int)] and
        @term[(types Γ (substitute e_2 x v) list)].
        Then by rule @rulename[cons], we have that
        @term[(types Γ (cons (substitute e_1 x v) (substitute e_2 x v)) list)].
        But @term[(cons (substitute e_1 x v) (substitute e_2 x v))] is
        @term[(substitute (cons e_1 e_2) x v)], so
        @term[(types Γ (substitute (cons e_1 e_2) x v) list)].}
 @item{@term[(types (extend Γ x t_x) (+ e_1 e_1) int)]: Then we know that
        @term[(types (extend Γ x t_x) e_1 int)] and
        @term[(types (extend Γ x t_x) e_2 int)].
        Then by the induction hypothesis,
        @term[(types Γ (substitute e_1 x v) int)] and
        @term[(types Γ (substitute e_2 x v) int)].
        Then apply rule @rulename[plus].}
 @item{@term[(types (extend Γ x t_x) (* e_1 e_2) int)]:
        as in the previous case.}
 @item{@term[(types (extend Γ x t_x) (car e_1) int)]: Then we know that
        @term[(types (extend Γ x t_x) e_1 list)]. Then by IH,
        @term[(types Γ (substitute e_1 x v) list)].
        And then by rule @rulename[car],
        @term[(types Γ (substitute (car e_1) x v) int)].}
 @item{@term[(types (extend Γ x t_x) (cdr e_1) list)]:
        As in the previous case.}
 @item{@term[(types (extend Γ x t_x) (let y e_1 e_2) t)]:
        Without loss of generality,
        we take @term[y] ≠ @term[x]. Then we know that
        @term[(types (extend Γ x t_x) e_1 t_e)] for some @term[t_e], and that
        @term[(types (extend (extend Γ x t_x) y t_e) e_2 t)].
        Then by the induction hypothesis,
        @term[(types Γ (substitute e_1 x v) t_e)].
        Because @term[x] ≠ @term[y], @term[(extend (extend Γ x t_x) y t_e)]
        = @term[(extend (extend Γ y t_e) x t_x)]. So we have that
        @term[(types (extend (extend Γ y t_e) x t_x) e_2 t)].
        Then by the induction hypothesis,
        @term[(types (extend Γ y t_e) (substitute e_2 x v) t)].
        Then @term[(types Γ (substitute (let y e_1 y_2) x v) t)] by rule
        @rulename[let].}
 @item{@term[(types (extend Γ x t_x) y (lookup (extend Γ x t_x) y))]:
  Then there are two possibilities,
  whether @term[x] = @term[y] or not:
  @itemlist[
   @item{If @term[x] = @term[y], then @term[(substitute y x v)] is @term[v].
            Furthermore, this means that @term[t] = @term[t_x]. And we
            have from the premise that @term[(types Γ v t_x)].}
   @item{If @term[x] ≠ @term[y], then @term[(substitute y x v)] is @term[y].
           Furthermore, we know that @term[(lookup (extend Γ x t_x) y)] =
           @term[(lookup Γ y)] = @term[t].
           Then @term[(types Γ y (lookup Γ y))].}
 ]}
]

QED.

Now we are ready to prove preservation:

@lemma[#:name "Preservation"] If @term[(types () e_1 t)] and
@term[(--> e_1 e_2)] then @term[(types () e_2 t)].

@proof[] By cases on the reduction relation:

@itemlist[
 @item{@term[(--> (in-hole E (+ n_1 n_2)) (in-hole E (meta-+ n_1 n_2)))]:
        By the replacement lemma, @term[(+ n_1 n_2)] must have some type,
        and by inversion, that type must be @term[int]. The result of the
        addition metafunction is also an integer with type @term[int]. Then
        by replacement, @term[(types () (in-hole E (meta-+ n_1 n_2)) t)].}
 @item{@term[(--> (in-hole E (* n_1 n_2)) (in-hole E (meta-* n_1 n_2)))]:
        as in the previous case.}
 @item{@term[(--> (in-hole E (car (cons v_1 v_2))) (in-hole E v_1))]:
        By the replacement lemma, @term[(types () (car (cons v_1 v_2)) t_e)]
        for some type @term[t_e]. The only rule that applies is @rulename[car],
        which requires that @term[t_e] = @term[int] and
        @term[(types () (cons v_1 v_2) list)]. This types only by rule
        @rulename[cons], which requires that @term[(types () v_1 int)].
        Then by replacement, @term[(types () (in-hole E v_1) t)].}
 @item{@term[(--> (in-hole E (cdr (cons v_1 v_2))) (in-hole E v_2))]:
        By the replacement lemma, @term[(types () (cdr (cons v_1 v_2)) t_e)]
        for some type @term[t_e]. The only rule that applies is @rulename[cdr],
        which requires that @term[t_e] = @term[list] and
        @term[(types () (cons v_1 v_2) list)]. This types only by rule
        @rulename[cons], which requires that @term[(types () v_2 list)].
        Then by replacement, @term[(types () (in-hole E v_2) t)].}
 @item{@term[(--> (in-hole E (let x v_1 e_22)) (in-hole E (substitute e_22 x v_1)))]:
        By the replacement lemma, @term[(types () (let x v_1 e_22) t_e)]
        for some types @term[t_e]. The only rule that applies is @rulename[let],
        which requires that @term[(types () v_1 t_x)] for some @term[t_x] such
        that @term[(types ([x t_x]) e_22 t_e)]. Then by the substitution lemma,
        @term[(types () (substitute e_22 x v_1) t_e)]. Then by replacement,
        @term[(types () (in-hole E (substitute e_22 x v_1)) t)].}
]

QED.

@subsubsection{Progress}

Before we can prove progress, we need to classify values by their types.

@lemma[#:name "Canonical forms"]

If @term[v] has type @term[t], then:
@itemlist[
 @item{If @term[t] is @term[int] then @term[v] is an integer literal
          @term[n].}
 @item{If @term[t] is @term[list], then either @term[v] = @term[nil]
          or @term[v] = @term[(cons v_1 v_2)] where
          @term[v_1] has type @term[int] and @term[v_2] has type @term[list].}
]

@proof[] By induction on the typing derivation of
@term[(types () v t)]:

@itemlist[
 @item{@term[(types () n int)]: Then @term[v] is an integer literal.}
 @item{@term[(types () nil list)]: Then @term[v] is the empty list.}
 @item{@term[(types () (cons e_1 e_2) list)]: By the syntax of values
        it must be the case that @term[e_1] is a value @term[v_1] having type
        @term[int], and @term[e_2] is a value @term[v_2] having type
        @term[list].}
 @item{@term[(types () (+ e_1 e_2) int)]: Vacuous, because not a value.}
 @item{The remaining cases are all vacuous because they do not allow for
  value forms.}
]

QED.

@lemma[#:name "Context replacement"]{If @term[(--> e_1 e_2)] then
@term[(--> (in-hole E e_1) (in-hole E e_2))]. If @term[(--> e_1 WRONG)]
then @term[(--> (in-hole E e_1) WRONG)].}

@proof[] If @term[(--> e_1 e_2)] then @term[e_1] must be some redex
in a hole: @term[(in-hole E_1 e_11)]. Furthermore, it must take a step to some
@term[(in-hole E_1 e_22)] = @term[e_2]. Then the same redex @term[e_11]
reduces to the same reductum @term[e_22] in any evaluation context, including
@term[(in-hole E E_1)].

If @term[(--> e_1 WRONG)] then @term[e_1] must be some redex in a hole:
@term[(in-hole E_1 e_11)] which reduces to @term[WRONG]. Then that same redex
reduces to @term[WRONG] in any evaluation context, including
@term[(in-hole E E_1)].

@lemma[#:name "Progress"]{If @term[(types () e t)] then
term @term[e] either reduces or is a value.}

@proof[] By induction on the typing derivation; by cases on the
conclusion:

@itemlist[
 @item{@term[(types () n int)]: Then @term[e] is a value.}
 @item{@term[(types () nil list)]: Then @term[e] is a value.}
 @item{@term[(types () (cons e_1 e_2) list)]:
   Then @term[(types () e_1 int)]
   and @term[(types () e_2 list)].
   By the induction hypothesis, term @term[e_1] either reduces, or is a value.
   If @term[e_1] reduces to some term @term[e_11], then
   @term[(--> (cons e_1 e_2) (cons e_11 e_2))] by the context replacement lemma.
   If @term[e_1] reduces to @term[WRONG], then
   @term[(--> (cons e_1 e_1) WRONG)] by the context replacement lemma.
   If @term[e_1] is a value @term[v_1], then consider @term[e_2], which by
   the induction hypothesis either reduces or is a value.
   If @term[e_2] reduces to a term @term[e_22], then
   @term[(--> (cons v_1 e_2) (cons v_1 e_22))] by the context replacement lemma.
   If @term[e_2] reduces to @term[WRONG], then
   @term[(--> (cons v_1 e_2) WRONG)] by the context replacement lemma.
   Finally, if @term[e_2] is a value @term[v_2] then @term[e]
   is a value @term[(cons v_1 v_2)].
 }
 @item{@term[(types () (+ e_1 e_2) int)]:
   Then @term[(types () e_1 int)]
   and @term[(types () e_2 int)].
   By the induction hypothesis, @term[e_1] either reduces or is a value.
   If @term[e_1] reduces to a term @term[e_11], then
   @term[(--> (+ e_1 e_2) (+ e_11 e_2))] by the context replacement lemma.
   If @term[e_1] reduces to @term[WRONG] then
   @term[(--> (+ e_1 e_2) WRONG)] by the context replacement lemma.
   If @term[e_1] is a value @term[v_1], then consider @term[e_1], which by
   the induction hypothesis either reduces or is a value.
   If @term[e_2] reduces to a term @term[e_22], then
   @term[(--> (+ v_1 e_2) (+ v_1 e_22))] by the context replacement lemma.
   If @term[e_2] reduces to @term[WRONG], then
   @term[(--> (+ v_1 e_2) WRONG)] by the context replacement lemma.
   Otherwise, @term[e_2] is a value @term[v_2]. By the canonical forms lemma,
   @term[v_1] is an integer @term[n_1] and @term[v_2] is an integer
   @term[n_2]. Thus, we can take the step
   @term[(--> (+ n_1 n_2) (meta-+ n_1 n_2))].
 }
 @item{@term[(types () (* e_1 e_2) int)]: As in the previous case.}
 @item{@term[(types () (car e_1) int)]:
   Then @term[(types () e_1 list)].
   By the induction hypothesis, @term[e_1] either reduces or is a value.
   If it reduces to a term @term[e_11], then
   @term[(--> (car e_1) (car e_11))] by the context replacement lemma.
   If it reduces to @term[WRONG], then
   @term[(--> (car e_1) WRONG)] by the context replacement lemma.
   Otherwise, @term[e_1] is a value. By the canonical forms lemma,
   it has the form @term[(cons v_1 v_2)], so we can take a step
   @term[(--> (car (cons v_1 v_2)) v_1)].
 }
 @item{@term[(types () (cdr e_1) list)]: As in the previous case,
   but reducing to @term[v_2].}
 @item{@term[(types () x t)]: Vacuous.}
 @item{@term[(types () (let x e_1 e_2) t)]:
   Then @term[(types () e_1 t_x)]
   and @term[(types ([x t_x]) e_2 t)] for some @term[t_x].
   Then by the induction hypothesis, @term[e_1] either reduces or is a value.
   If @term[e_1] reduces to a term @term[e_11], then
   @term[(--> (let x e_1 e_2) (let x e_11 e_2))] by the context replacement lemma.
   If @term[e_1] reduces to @term[WRONG] then
   @term[(--> (let x e_1 e_2) WRONG)] by the context replacement lemma.
   Otherwise, @term[e_1] is a value @term[v_1], and
   @term[(--> (let x v_1 e_2) (substitute e_2 x v_1))].}
]

QED.

@exercise{Prove progress and preservation for your language extended with
          Booleans.}

@exercise{Prove progress and preservation for your language extended with
          generic lists.}

@exercise{Are the previous two exercises orthogonal? How do they interact
          or avoid interaction?}

@section{Termination}

Now let’s prove a rather strong property about a rather weak language.

We're going to do induction on @emph{the size of terms} rather than
the structure of terms, and we're going to use a particular size function,
defined as:
@centered{
  @with-rewriters[@render-metafunction[r:size]]
}

@lemma[#:name "Size of values"]{For all values, @term[(size v)] = 0.}

@proof[] Exercise.

@theorem[#:name "Size is work"]{
Suppose @term[(types () e t)] and
@term[(size e)] = k. Then @term[e] either reduces to a value or goes wrong in
k or fewer steps.
}

@proof[] By induction on k. By cases on terms:

@itemlist[
 @item{@term[n]: Then k = 0, and @term[e] reduces to value @term[n] in 0 steps.}
 @item{@term[nil]: Also k = 0.}
 @item{@term[(cons e_1 e_2)]. Then by inversion of @rulename[cons],
        @term[(types () e_1 int)] and @term[(types () e_2 list)].
        Let j be the size of @term[e_1]; then the size of @term[e_2] is
        k – j.
        Then by the induction hypothesis, @term[e_1] reduces to a value
        @term[v_1] or to @term[WRONG] in j or fewer steps.
        If it reduces to @term[WRONG] then
        by the context replacement lemma, @term[(cons e_1 e_2)] also reduces
        to @term[WRONG] in j or fewer steps.
        Otherwise, consider the induction hypothesis on
        @term[e_2] (size k – j);
        it must reduce to a value @term[v_2] or to @term[WRONG] in k – j or
        fewer steps.
        If @term[WRONG], then the whole thing goes wrong by context replacement.
        Otherwise, @term[(cons e_1 e_2)] goes to @term[(cons v_1 v_2)] in
        k or fewer steps.}
 @item{@term[(+ e_1 e_2)]. Then by inversion of the typing rule @term[int], both
        subterms have type @term[int]. Let j be the size of @term[e_1]; then
        the size of @term[e_1] is k – j – 1.
        Then by the induction hypothesis, each
        reduces to a value or goes wrong, in at most j and k - j - 1 steps
        respectively. If either goes wrong, then the whole
        term goes wrong because both @term[(+ hole e_2)] and @term[(+ v_1 hole)]
        are evaluation contexts. Otherwise, by the canonical values lemma both
        values must be numbers @term[n_1] and @term[n_2]. Because
        @term[(-->* e_1 n_1)] in j or fewer steps, by context replacement
        @term[(-->* (+ e_1 e_2) (+ n_1 e_2))] in j or fewer steps.
        And because
        @term[(-->* e_2 n_2)] in k - j - 1 or fewer steps,
        by context replacement again
        @term[(-->* (+ n_1 e_2) (+ n_1 n_2))]
        in k – j – 1 or fewer steps.
        Then in one more step
        @term[(--> (+ n_1 n_2) (meta-+ n_1 n_2))], which is a value.
        The total number of steps has been k or fewer.}
 @item{@term[(* e_1 e_2)]: As in the previous case, m.m.}
 @item{@term[(car e_1)] and @term[(cdr e_1)]: In either case, the subterm
        @term[e_1] must have type @term[list] by inversion of the typing rule.
        Furthermore, the size of @term[e_1] must be k – 1.
        Then by the induction hypothesis, @term[e_1] either reduces to a value
        or goes wrong in k – 1 or fewer steps.
        If it goes wrong then the whole term goes wrong.
        If it reduces to a value, then by preservation, that value also has
        type @term[list]. (Note also that it also reduces to a value in the
        evaluation context @term[(car hole)].)
        Then by the canonical values lemma, that value
        must be either @term[nil] or @term[(cons v_1 v_2)] for some values
        @term[v_1] and @term[v_2]. If the former then the whole term goes to
        @term[WRONG] in one more step by rule @rulename[car-nil] or rule
        @rulename[cdr-nil],
        respectively. If the latter, then it take one more step to
        @term[v_1] or @term[v_2], respectively. In either case, k steps have
        transpired.}
  @item{@term[x]: Vacuous because open terms don't type.}
  @item{@term[(let x e_1 e_2)]: By inversion, we know that
        @term[(types () e_1 t_x)] for some type @term[t_x]. And we know that
        @term[(types ([x t_x]) e_2 t)].
        Let j be the size of @term[e_1]; then the size of @term[e_2] is
        k – j – 1. By the induction hypothesis on term @term[e_1],
        we have that @term[e_1] reduces to a value or goes wrong in j or fewer
        steps. If it goes wrong then the whole term goes wrong. If it reduces to
        a value @term[v_1], then by context replacement (and induction on the
        length of the reduction sequence), the whole term reduces
        @term[(-->* (let x e_1 e_2) (let x v_1 e_2))] in j or fewer steps.
        Then in one more step,
        @term[(--> (let x v_1 e_2) (substitute e_2 x v_1))].
        Note that because the size of a variable is 0 and so is the size of
        a value, the size of @term[(substitute e_2 x v_1)] is the same as
        the size of @term[e_2], k – j – 1. Further note that by preservation,
        @term[(types () (substituted e_1 x v_1) t)]. So we an apply the
        induction hypothesis to @term[(substituted e_1 x v_1)], learning that
        it goes wrong or reaches a value in k – j – 1 or fewer steps.
        This yields a total of k or fewer steps.}
]

QED.
