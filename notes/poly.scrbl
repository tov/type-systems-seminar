#lang scribble/base

@(require (prefix-in r: "redex/poly.rkt")
          (prefix-in stlc: "redex/stlc.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:system-f)
@define[system-f]{@langname[System-F]}

@title{The Polymorphic Lambda Calculus @system-f}

Suppose we want to write the composition function in the simply-typed
lambda calculus. What does it look like? Well, it depends on the types
of the functions. We can compose two @term[(-> nat nat)] functions with this:
@;
@centered[
    @term[(λ x_1 (-> nat nat) (λ x_2 (-> nat nat) (λ y nat (ap x_1 (ap x_2 y)))))]
]
@;
But if the functions have different types, we will need to define a
different composition function. This is awkward!

Polymorphism lets us write one composition function that works for any types:
@;
@centered[
    @term[(Lam a_1 (Lam a_2 (Lam a_3 (lam x_1 (-> a_2 a_3) (lam x_2 (-> a_1 a_2) (lam y a_1 (app x_1 (app x_2 y))))))))]
]
@;
We model polymorphism with @|system-f|.

@section[#:tag "system-f-syntax"]{Syntax}

@render-nonterminals[r:system-f t e]

@section[#:tag "system-f-dynamics"]{Dynamic Semantics}

The give the dynamic semantics of @system-f, we first define evaluation
contexts:

@render-nonterminals[r:system-f E]

Then the reduction relation has two rules, one for value abstraction
applications, and one for type abstraction applications:

@render-reduction-rules[r:->val β-val inst]

@section[#:tag "system-f-statics"]{Static Semantics}

To give the static semantics of @system-f, we have both type variable
environments (which tell us which type variables are in scope) and
typing environments (which map variables to their types):

@render-nonterminals[r:system-f Δ Γ]

The main typing judgment relies on two auxiliary judgments. The
first tells us whether a type is well formed (which just means closed
for this language):

@render-judgment-rules[r:kinds var var arr all]

A typing environment is well formed when all the types in it are well formed:

@render-judgment-rules[r:kinds/env nil cons]

Finally, we give the typing judgments for @|system-f|:

@render-judgment-rules[r:types var app abs t-abs t-app]
