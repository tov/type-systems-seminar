#lang scribble/base

@(require (prefix-in r: "redex/poly.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:system-f)
@define[system-f]{@langname[System-F]}

@title{The Polymorphic Lambda Calculus @system-f}

@section{Syntax}

@render-nonterminals[r:system-f t e]

@section{Dynamic Semantics}

The give the dynamic semantics of @system-f, we first define evaluation
contexts:

@render-nonterminals[r:system-f E]

Then the reduction relation has two rules, one for value abstraction
applications, and one for type abstraction applications:

@render-reduction-rules[r:->val β-val inst]

@section{Static Semantics}

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
