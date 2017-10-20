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

@section{Static Dynamics}

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

@subsection{Type Safety}

The goal of our type system is to prevent undetected errors—that is,
stuck terms—in our programs. To show that it does this, we will prove
@italic{type safety}: if a term @term[e] has a type @term[t], then
one of:
@;
@itemlist[
  @item{It will reduce in some number of steps to a value @term[v] such
        that that has type @term[t].}
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

@subsubsection{Progress}
