#lang scribble/base

@(require (prefix-in r: "redex/lcube.rkt")
          (prefix-in sysf: "redex/sysf.rkt")
          "util.rkt"
          (only-in redex/reduction-semantics default-language)
          redex/pict)

@(default-language r:λcube)
@(define λcube @langname[λ-cube])

@title{The Lambda Cube: @λcube}

The @λcube provides a systematic organization of types
systems that captures a range of expressiveness, from the
simply-typed lambda calculus (in @secref["sec:stlc"]) though
the polymorphic lambda calculus (in @secref["sec:sysf"]), the
higher-order lambda calculus (in @secref["sec:fomega"]), and
up to λC, the calculus of construction (which is the focus
of this section).

@section[#:tag "lcube-syntax"]{Syntax}

The basic idea of the structure is to eliminate the distinction
between types and terms and then use typing judgments
to control which classes of expression are allowed in type
positions. To get started, we first just get rid of the
distinction between types and terms using this syntax:

@render-nonterminals[r:λcube e τ s]

The first three expression forms are the familiar variables,
lambda abstractions, and application expressions. The @term[Π]
expression form represents a dependent function type. That is,
the type @term[(Π (x : τ_1) τ_2)] (where @term[x] does not
appear free in @term[τ_2]) represents functions from @term[τ_1]
to @term[τ_2]. The @term[*] is the type of types, just
as in @secref["sec:sysf"], and @term[□] is analgous, but one level up.
That is, it represents the type of kinds or, expressions that have
the type @term[□] are expressions that themselves compute kinds.

To get a feel for how this notation specializes to the earlier
type systems we considered, let us revist the example from the
the beginning of @secref["sec:sysf"], the polymorphic function
composition. Here's the original version of the function:

@term[(Λ a_1
         (Λ a_2
            (Λ a_3
               (λ x_1 (-> a_2 a_3)
                 (λ x_2 (-> a_1 a_2)
                   (λ y a_1
                     (ap x_1 (ap x_2 y))))))))
      #:lang sysf:λ-2]

In the new language, the @term[Λ] and @term[λ] are not distinguished
by the constructor, but a @term[Λ] is the same thing as a @term[λ] where
the argument has type @term[*]:

@term[(λ (a_1 : *)
        (λ (a_2 : *)
          (λ (a_3 : *)
            (λ (x_1 : (-> a_2 a_3))
              (λ (x_2 : (-> a_1 a_2))
                (λ (y : a_1)
                  (ap x_1 (ap x_2 y))))))))]

We also adjust the syntax to require an extra set of parentheses and a colon
to make it a little bit easier to read expressions (becuase other distinctions
are removed).

