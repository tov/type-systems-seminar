#lang scribble/base

@(require (prefix-in r: "redex/let-nl.rkt")
          (only-in redex default-language)
          redex/pict)

@(default-language r:let-nl)

@(define-syntax-rule (term e) (render-term (default-language) e))

@define[let-nl]{let-nl}

@title{The @let-nl Language}

The @let-nl language has expressions @term[e] defined as follows:

@render-language[r:let-nl]

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
we will define its dynamic semantics using a rewriting system.

@render-reduction-relation[r:->val #:style 'horizontal]

@render-language[r:let-nl/eval]