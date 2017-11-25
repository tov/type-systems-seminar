#lang scribble/base

@(require (prefix-in r: "redex/fomega.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:fomega)
@define[fomega]{@langname[λ-ω]}

@title{The higher-order lambda calculus @fomega}

@section[#:tag "fomega-syntax"]{Syntax}

The higher-order calculus @fomega extends System F with type operators, that
is, functions at the type level:
@;
@render-nonterminals[r:fomega t]
@;
In addition to type variables, functions, and universal types (all from System
F), we now have abstraction of types over types (@term[(λ a k t)]) and
application of types to types (@term[(ap t_1 t_2)]).

In order to avoid errors at the type computation level, we now have “types of
types,” known as @italic{kinds}:
@;
@render-nonterminals[r:fomega k]
@;
There are two kind constructors. Kind @term[*] is the kind of proper types,
that is, types that can be the types of terms. Kind @term[(=> k_1 k_2)] is
the kind of a type operator that consumes types of kind @term[k_1] and produces
types of kind @term[k_2]. For example, the type constructor @term[List] has
kind @term[(=> * *)]—apply it to a term with a type of kind @term[*], like
@term[Int], and you get @term[(List Int)], a type of kind @term[*], back.

Note that types in @fomega are a copy of the terms of STLC in the type level,
with one base kind @term[*].

Terms in @fomega are the same as terms in System F, except that
the type variable in @term[(Λ a k e)] is decorated with a kind:
@;
@render-nonterminals[r:fomega e]

In fact, all three forms that bind type variables decorate them with a kind.

@section[#:tag "fomega-dynamics"]{Dynamic semantics}

The dynamics for @fomega are straightforward. Values and evaluation contexts
are as in System F:
@;
@render-nonterminals[r:fomega v E]

There are two reduction rules, as in System F, for applications of λs and
instantiations of Λs:
@;
@render-reduction-rules[r:->val β-val inst]

@section[#:tag "fomega-statics"]{Static semantics}

@fomega's type system is more complex than what we’ve seen before for two
reasons: we are now doing computation at the type level and we now need to
kind-check types.

Kind checking tells us that a type is well-formed in a context that binds
type variables to their kinds. However, we will use the same contexts
for type checking, so we will bind term variables to types and type variables
to kind in the same context:
@;
@render-nonterminals[r:fomega Γ]

Then the kinding rules are like STLC at the type level:
@;
@render-judgment-rules[r:kinds var arr all abs app]
@;
Note that @term[→] and @term[all] form types of kind @term[*] from
types of kind @term[*].

In order to type check terms, we need a notion of type equivalence
that includes computation in types. The usual theoretical way to do this
is to define equivalence as a congruence that includes beta reduction:
@;
@render-judgment-rules[r:≡ refl sym trans arr all abs app β]

Then in the type rules, we would check that types that in other systems need
to be equal are equivalent. However, to type check algorithmically, we instead
define type computation in terms of type evaluation
contexts and then β reduction over types:
@;
@render-nonterminals[r:fomega TE]
@;
@render-reduction-rules[r:->type β-type]

Then to compare two types, we fully reduce both of them and compare for
equality. This happens in the rules for application and instantiation.
@;
@render-judgment-rules[r:types var abs app tabs tapp]