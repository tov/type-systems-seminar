#lang scribble/base

@(require (prefix-in r: "redex/qual.rkt")
          (only-in "redex/qual.rkt" get-evidence)
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λ-qual)
@define[λ-qual]{@langname[λ-qual]}

@title{Qualified types}

In the previous lecture, we saw how ML infers types for programs that
lack type annotations. In this lecture, we see how to extend ML with a
principled form of overloading, similar to how it appears in Haskell and
Rust. In particular, we will extend type schemes to a form
@term[(all (a ...) (=> P t))],
where @term[P] is a logical formula over types that must be
satisfied to use a value having that type scheme.

@section[#:tag "qual-syntax"]{Syntax}

Our language includes the usual variables, lambda abstractions,
applications, and let from ML, as well as some constants, a condition
form, and pairs:
@;
@render-nonterminals[r:λ-qual e]

The constants include integers, and functions for projecting from pairs,
subtraction, equality, and less-than:
@;
@render-nonterminals[r:λ-qual c z]

@section[#:tag "qual-dynamic"]{Dynamic semantics}

Values include constants, lambdas, and pairs of values:
@;
@render-nonterminals[r:λ-qual v]

Evaluation contexts are standard, performing left-to-right evaluation
for applications and pairs:
@;
@render-nonterminals[r:λ-qual E]

We give a reduction relation that includes rules for application and
let, two rules for if0 (true and false), and delta, which handles
applications of constants by delegating to a metafunction:
@;
@render-reduction-rules[r:->val β-val let if-true if-false delta]

The metafunction @term[δ] gives the results for applying constants
to values:
@;
@render-metas[r:δ]
@;
Note that the functions represented by constants are uncurried, taking
pairs of values—this simplifies our presentation somewhat.

@section[#:tag "qual-static"]{Static semantics}

As in ML the static semantics assigns prenex type schemes to let-bound
values, but type schemes now have an additional component. The syntax of
types is as follows.

@subsection[#:tag "qual-type-syntax"]{Syntax of types}

Monotypes include type variables, the base type @term[Int], product
types, and function types:
@;
@render-nonterminals[r:λ-qual t]

To represent overloading, we define a fixed set of @italic{type classes}
@term[C], which are used to construct @italic{predicates} on types
@term[π]:
@;
@render-nonterminals[r:λ-qual C π]
@;
For any type @term[t], the predicate @term[(Eq t)] means that type
@term[t] supports equality, and the predicate @term[(Ord t)] means that
type @term[t] supports less-than. In a real system, the set of type
classes (and thus the possible predicates) would be extensible by the
user.

A @italic{predicate context} @term[P] is a collection of predicates:
@;
@render-nonterminals[r:λ-qual P]

Then a @italic{qualified type} @term[ρ] is a monotype qualified by some
predicate context:
@;
@render-nonterminals[r:λ-qual ρ]

Then a type scheme is a qualified type generalized over some quantified set
of type variables:
@;
@render-nonterminals[r:λ-qual as σ]
@;
For example, type scheme
@term[(all (a) (=> [(Eq a)] (-> a (-> a Int))))]
describes a function that takes (curried) two arguments of any
type @term[a] supporting equality and returns an integer.

As in ML, typing environments map variable names to type schemes:
@;
@render-nonterminals[r:λ-qual Γ]

@subsection[#:tag "qual-const-types"]{The types of constants}

We can now define the @term[type-of] metafunction, which gives type
schemes for the constants:
@;
@render-metas[r:type-of]
@;
Note that @term[=] and @term[<] are overloaded.

@subsection[#:tag "qual-inst-entail"]{Instantiation and entailment}

Before we can give our main typing relation, we need two auxiliary
judgments. The first, as in ML, relates a type scheme to its instantiations
as qualified types:
@;
@render-judgment-rules[r:> mono all]

The second relation is entailment for predicate contexts. This is not
strictly necessary (and omitted from Jones’s paper), but allows us to
make predicate contexts smaller when they are redundant. The first two
rules rule say that a predicate context entails itself and that
entailment is transitive.
@;
@render-judgment-rules[r:qimplies refl trans]

The next rule says that we can remove duplicate predicates from a context:
@;
@render-judgment-rules[r:qimplies dup]

The next two rules say that integers support equality and ordering, and
that fact need not be recorded in the context to prove it:
@;
@render-judgment-rules[r:qimplies eq-int]
@render-judgment-rules[r:qimplies ord-int]

Finally, equality works on pairs if it works on both components of the pair:
@;
@render-judgment-rules[r:qimplies eq-prod]

@subsection[#:tag "qual-stx-types"]{Syntax-directed typing}

The typing judgment is of the form @term[(qtypes P Γ e t)], where
@term[P] gives constraints on the types in @term[Γ]. Even though it
appears on the left, @term[P] should be thought of as an out-parameter.

The rule for typing a variable says to look up its type scheme in the
environment and then instantiate the bound variables of the type scheme.
The predicate context @term[P] from the instantiated type scheme becomes
the predicate context for the judgment:
@;
@render-judgment-rules[r:qtypes var-inst]

Typing a constants is substantially the same, except we get its type
scheme using the @term[type-of] metafunction:
@;
@render-judgment-rules[r:qtypes const-inst]

The rules for lambda abstractions, applications, conditionals, and
pairs, as the same as they would be in ML, except that we thread through
and combine the predicate contexts:
@;
@render-judgment-rules[r:qtypes abs app if0 pair]

Finally, the let rule is where the action is:
@;
@render-judgment-rules[r:qtypes let-gen]

First we type @term[e_1], which produces a predicate context @term[P_1].
Then we apply the entailment relation to reduce @term[P_1] to a context
that entails it, @term[P]. (This step can be omitted, but it reflects
the idea that we probably want to simplify predicate contexts before
including them in type schemes.) Then we build a type scheme @term[σ] by
generalizing all the type variables in @term[P] and @term[t_1] that do
not appear in @term[Γ], and bind that @term[σ] in the environment to
type @term[e_2]. Note that the resulting predicate context for the
judgment is only @term[P_2], the constraints required by @term[e_2],
since the constraints required by @term[e_1] are carried by the
resulting type scheme.

Alternatively, we could split the predicates of @term[P_1] (or @term[P])
into those relevant to @term[t_1], which we would package up in the type
scheme, and those irrelevant to @term[t_2], which we would propogate
upward.

@section[#:tag "qual-inference"]{Type inference algorithm}

The above type system provides a satisfactory account of which terms
type and which do not, but it does not give us an algorithm that we can
actually run. In this section, we extend ML’s Algorithm W for qualified
types.

First, we give a helper metafunction for instantiating a type scheme
with fresh type variables:
@;
@render-metas[r:inst]

Again we use unification. Because unification is applied to monotypes,
it is the same as in ML (except now we have to handle product types as
well):
@;
@render-judgment-rules[r:unify var-same var-left var-right int prod arr]

Algorithm W for qualified types takes a type environment and a term, and
returns a substitution, a type, and a predicate context:
@term[(W Γ e S t P)].

To infer the type of a variable or constant, we look up its type scheme
(in the environment or the @term[type-of] metafunction, respectively)
and instantiate it with fresh type variables, yielding a qualified type
@term[(=> P t)]. The @term[t] is the type of the variable or constant,
and @term[P] is the predicate context that must be satisfied:
@;
@render-judgment-rules[r:W var const]

Lambda abstraction, application, pairing, and the conditional are as
before, merely propagating and combining predicate contexts:
@;
@render-judgment-rules[r:W abs app pair if0]
@;
Note how substitutions must be applied to predicate contexts, just as we
apply them to type environments and types.

Finally, the let rule follows the let rule from the previous section,
packaging up the predicate context generated for @term[e_1] in the type
scheme assigned to @term[x]. We (optionally) assume a metafunction
@term[(r:qreduce P)] that simplifies the predicate context before
constructing the type scheme.
@;
@render-judgment-rules[r:W let]

@section[#:tag "qual-evidence"]{Evidence translation}

@exercise{
What is the most general type scheme of the term
@term[(λ (x) (λ (y) (if0 (= (pair x y)) x y)))]?
}

How would you implement such a function—in particular, how does it
figure out the equality for a generic/unknown type parameter? Well, our
operational semantics cheated by relying on Racket’s underlying
polymorphic @tt{equal?} function. Racket's @tt{equal?} relies on
Racket's object representations, which include tags that distinguish
number from Booleans from pairs, etc. But what about in a typed language
that does not use tags and thus cannot support polymorphic equality?

One solution is called evidence passing, wherein using a qualified type
requires passing evidence that it is inhabited, where this evidence
specifies some information about how to perform the associated
operations. In our type classes example, the evidence is the equality or
less-than function specialized to the required type. (In a real
evidence-passing implementation such as how Haskell is traditionally
implemented, the evidence is a dictionary of methods.)

We can translate implicitly-typed @λ-qual programs like the above into
programs that pass evidence explicitly. We do this by typing them in an
evidence environment, which names the evidence for each predicate:
@;
@render-nonterminals[r:λ-qual Δ]

We can use the evidence environment to summon or construct evidence if
it's available. In particular, the judgment @term[(get-evidence Δ e π)]
uses evidence environment @term[Δ] to construct @term[e], which is
evidence of predicate @term[π]. In particular, if @term[π] is
@term[(Eq t)] then @term[e] should be an equality function of type
@term[(-> (Prod t t) Int)]; if @term[π] is @term[(Ord t)] then @term[e]
should be a less-than function of type @term[(-> (Prod t t) Int)].

For base type @term[Int], the evidence is just a primitive function
performing the correct operation:
@;
@render-judgment-rules[r:get-evidence eq-int ord-int]

For a product type, we summon evidence for each component type, and then
construct the equality function for the product.
@;
@render-judgment-rules[r:get-evidence eq-prod]

Other types are looked up in the evidence environment:
@;
@render-judgment-rules[r:get-evidence lookup]
@;
Note that if difference evidence appears for the same repeated
predicate, then the behavior can be incoherent.

The evidence translation uses two more auxiliary judgments. The first is
for applying a term that expect evidence to its expected evidence:
@;
@render-judgment-rules[r:app-evidence nil cons]

The second abstracts over the evidence expected by a term based on its
context:
@;
@render-judgment-rules[r:abs-evidence nil cons]

Four rules of the typing judgment are unremarkable, simply passing the
evidence environment through and translating homomorphically:

@render-judgment-rules[r:qtranslates abs app if0 pair]

The rules for variables and constants take a polymorphic value and apply
it to the required evidence for any predicates contained in its
qualified type, using the evidence application judgment:
@;
@render-judgment-rules[r:qtranslates var const]

The let form, as above, generalizes, by abstracting the right-hand side
@term[e_1] over evidence corresponding to its inferred evidence context:
@;
@render-judgment-rules[r:qtranslates let]

@exercise{Rust uses monomorphization to implement generics and traits.
It does this by duplicating polymorphic code, specializing it at each
required type. Write a relation that formalizes monomorphization for
describes @|λ-qual|.}
