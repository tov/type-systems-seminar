#lang scribble/base

@(require (prefix-in r: "redex/lcube.rkt")
          (prefix-in sysf: "redex/sysf.rkt")
          "util.rkt"
          (prefix-in redex: redex/reduction-semantics)
          redex/pict)

@(define-syntax-rule
   (define-term (x y) e)
   (begin
     (define x (parameterize ([redex:default-language r:λcube])
                 (redex:term e)))
     (define y (parameterize ([redex:default-language r:λcube])
                 (term e)))))

@(redex:default-language r:λcube)
@(define λcube @langname[λ-cube])

@title{The Lambda Cube: @λcube}

The @λcube provides a systematic organization of types
systems that captures a range of expressiveness, from the
simply-typed lambda calculus (in @secref["sec:stlc"]) through
the polymorphic lambda calculus (in @secref["sec:sysf"]), the
higher-order lambda calculus (in @secref["sec:fomega"]), and
up to λC, the calculus of constructions, which is the focus
of this section.

@section[#:tag "lcube-syntax"]{Syntax}

The basic idea of the structure of the λ cube is to eliminate the distinction
between types and terms and then use typing judgments
to control which classes of expression are allowed in type
positions. To get started, we first just get rid of the
distinction between types and terms using this syntax:

@render-nonterminals[r:λcube e τ s]

The first three expression forms are the familiar variables,
lambda abstractions, and application expressions. The
@term[*] is the type of types, just as in
@secref["sec:sysf"], and @term[□] is analgous, but one level
up. That is, it represents the type of kinds or, expressions
that have the type @term[□] are expressions that themselves
compute kinds.

The final expression form, @term[→], represents function
types, but it is dependent. In its simplest form, the type
@term[(x : τ_1 → τ_2)], where @term[x] does not appear
free in @term[τ_2], represents functions from @term[τ_1] to
@term[τ_2]. In general, however, the variable @term[x] can appear
free in @term[τ_2], meaning that the type of the result of the
function can depend on the argument actually supplied to the
function.

This notation specializes to the earlier type systems we
considered; as an example, recall the function composition
operator from the beginning of @secref["sec:sysf"].
Here's the original version of the function:

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
the argument has type @term[*]. So, this is the composition operator
in @|λcube|:

@(define-term (composition-term composition-pict)
   (λ (a1 : *)
     (λ (a2 : *)
       (λ (a3 : *)
         (λ (x1 : (i2 : a2 → a3))
           (λ (x2 : (i1 : a1 → a2))
             (λ (y : a1)
               (ap x1 (ap x2 y)))))))))

@composition-pict

@(unless (redex:judgment-holds (r:types • ,composition-term any))
   (error 'lcube.scrbl "composition doesn't typecheck"))

We also adjust the syntax to require an extra set of
parentheses and a colon to make it a little bit easier to
read expressions (because other distinctions are removed).

Another example that's worth considering is the identity function.
Here it is:

@(define-term (id-term id-pict)
   (λ (α : *)
     (λ (x : α)
       x)))

@(define id-type (redex:term (α : * → (x : α → α))))
@(define id-types (redex:judgment-holds (r:types • ,id-term any) any))

@(unless (and id-types (= 1 (length id-types)))
   (error 'lcube.scrbl "id-types wrong: ~s" id-types))
@(unless (redex:alpha-equivalent? r:λcube id-type (list-ref id-types 0))
   (error 'lcube.scrbl "id-type wrong: ~s vs ~s"
          id-type (list-ref id-types 0)))


@id-pict

This term is what you would expect, simply replacing the capital Λ
with the lowercase λ and adding a @term[*]. But consider its type:

@(term->pict/pretty-write r:λcube id-type)

This is a type that cannot be expressed with just the arrow. Or, in
other words, this is a dependent type because the variable bound by the outer
function type is used in its body. It is the same as the type
@term[(all α (-> α α)) #:lang sysf:λ-2]
but we can use @term[→] for both the function type and for the
@term[all #:lang sysf:λ-2] type.

@section[#:tag "lcube-types"]{Typing Rules}

First, we just assert that @term[*] is a
@term[□]
@render-judgment-rules[r:types "axiom"]

and then we have what appears to be the standard variable rule:
@render-judgment-rules[r:types "variable"]
but note the premise that ensures that the environment is well-formed.
In earlier type systems, that was a self-contained check that
the types were well-formed. Now, because we have eliminated
the distinction between types and terms, it uses the typing
judgment itself:
@render-judgment-rules/horiz[r:env-ok "nil" "cons"]

The application rule handles all forms of abstraction:
@render-judgment-rules[r:types "application"] It looks
something like a combination of the application and type
application rule from λ-2. Like the normal function
application rule, we make sure that the two subexpressions
have appropriate types: one a function
and one a matching argument type (the type
in the parameter of the function type). Like the type
application rule, however, we perform a substitution,
computing the type of the result of the function based on
the argument that was actually supplied.

Sometimes, the type @term[A] that we get on the
function is different than the type @term[A] on the
argument. This rule allows us to do some computation
in order to make two such types match up to each other,
where the @term[≡] relation allows us to perform
@term[β] substitutions in the types as needed.
@render-judgment-rules[r:types/alt "conversion"]

In order to type check a @term[λ] abstraction, 
@render-judgment-rules[r:types "abstraction"]
we check the body, on the assumption that the
argument has the type on the @term[λ]. The second
premise ensures that the type that we get for the
result itself makes sense.

The final rule covers function type expressions.
@render-judgment-rules[r:types "λC"] This version allows
either @term[*] or @term[□] for both the argument and the
result type. This generality allows us to capture the
full Calculus of Constructions, which forms the basis for
the theorem proving system Coq.

If we restrict the rule so that both @term[s_1] and
@term[s_1] are @term[*], then the resulting type system is
equivalent to the simply-typed lambda calculus. Intuitively,
this restriction means that our functions can accept
arguments that are values, i.e., can be described by types,
but not by kinds.

If we allow @term[s_1] to be either @term[*] or @term[□],
but restrict @term[s_2] so it can be only @term[*], we get
the polymorphic lambda calculus, @langname[λ-2]. This means
that functions can now play the role of
@term[all #:lang sysf:λ-2], expressions, accepting types,
but always returning only a type. Various other restrictions
in this spirit correspond to various other type systems in
the literature.
