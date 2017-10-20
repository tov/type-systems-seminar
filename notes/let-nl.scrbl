#lang scribble/base

@(require (prefix-in r: "redex/let-nl.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:let-nl)
@define[let-nl]{@langname[let-nl]}

@title{The @let-nl Language}

The @let-nl language has expressions @term[e] defined as follows:

@centered{
 @render-language[r:let-nl]
}

There are two kinds of literal expressions, integers @term[n] and the empty
list @term[nil]. Additionally, we build longer lists with @term[(cons e_1 e_2)],
which is our traditional cons that creates a linked list node with first and
rest. We have two elimination forms for integers,
@term[(+ e_1 e_2)] and @term[(* e_1 e_2)].
Additionally, we have elimination forms for lists, @term[(car e)] and
@term[(cdr e)]. Finally, we have variables @term[x], and we have a form of
sharing in @term[(let x e_1 e_2)], which binds @term[x] to the value of
@term[e_1] in @term[e_2].

We might have a decent guess as to what this language means, but to be precise,
we will define its dynamic semantics using a rewriting system.  The reduction
relation describes a single computation step, and has a case for each kind of
basic computation step that our language performs. For example, here is how we
perform addition:

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
@;
We have two rules for getting the first and rest of a list:
@;
@render-reduction-rules[r:->val car cdr]
@;
These say that if we have a cons (pair) of values @term[(cons v_1 v_2)] then
@term[car] extracts the first value @term[v_1] and @term[cdr] extracts the
second value @term[v_2].
@;
There are also two rules that say what @term[car] and @term[cdr] do when given
@term[nil], the empty list:
@;
@render-reduction-rules[r:->val car-nil cdr-nil]
@;
Finally, the rule for @term[let] involves substituting the value for the
variable in the body:
@;
@render-reduction-rules[r:->val let]

In order to describe where evaluation can happen when when it is finished, we
extend our syntax with values @term[v] and evaluation context @term[E]:

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

