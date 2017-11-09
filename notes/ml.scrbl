#lang scribble/base

@(require (prefix-in r: "redex/ml.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λ-ml)
@define[λ-ml]{@langname[λ-ml]}

@title{ML type inference}

@section[#:tag "ml-syntax"]{STLC revisited}

We revisit the simply-typed λ calculus, but with several twists:
@itemlist[
 @item{We remove base types such as @term[nat] (for now) in favor of
  uninterpreted type variables @term[a].}
 @item{We add @term[let] expressions.}
 @item{Most importantly, we leave types @emph{implicit}.}
]

Here is the syntax of the resulting system:
@;
@render-nonterminals[r:λ-ml/no-bool t a b e x y]

@subsection[#:tag "ml-dynamic"]{Dynamic semantics}

The only values are λ abstractions:
@;
@render-nonterminals[r:λ-ml/no-bool v E]

The dynamic semantics of this language includes two reduction rules:
@;
@render-reduction-rules[r:->val β-val let]
@;
Note this means that dynamically we can consider @term[(let x e_1 e_2)]
as syntactic sugar for @term[(ap (λ x e_2) e_1)].

@subsection[#:tag "ml-static"]{Static semantics}

The static semantics should be familiar from the simply-typed lambda calculus,
since it's the same but for one thing: the rule for @term[λ] has to “guess” the
domain type @term[t_1].
@;
@render-judgment-rules[r:types var abs app let]

Here’s how it works: To type a λ expression, choose any type—made out of
type variables and arrows—for the parameter that lets you type the body.
For example, these are all valid judgments for the identity function:
@;
@itemlist[
 @item{@term[(types • (λ x x) (-> a a))]}
 @item{@term[(types • (λ x x) (-> (-> a a) (-> a a)))]}
 @item{@term[(types • (λ x x) (-> (-> a b) (-> a b)))]}
]
@;
Whatever type it’s given, it returns the same type. How a variable is used
may constrain its type. For example, to type @term[(λ x (λ y (ap y x)))] we
have to guess types for @term[x] and @term[y] such that @term[y] can be applied
to @term[x]. Suppose we guess @term[a] for @term[x]. Then we are faced with
choosing a type for @term[y] that can be applied to that, like say
@term[(-> a b)]. Then we get the type @term[(-> a (-> (-> a b) b))] for the
whole term. Those aren't the only types we could have chosen, however, For
example, we could choose @term[(-> a b)] for @term[x]; then @term[y] could be
any arrow type @term[(-> (-> a b) t)] for any type @term[t].

@exercise{Find types for these terms:}
@itemlist[
 @item{@term[(λ x (λ y x))]}
 @item{@term[(λ f (λ g (λ x (ap f (ap g x)))))]}
 @item{@term[(let f (λ x x) (ap f (λ x (λ y x))))]}
]

@exercise{Find a closed term that has no type. What is the only cause of type
 errors in this system?}

@subsection[#:tag "ml-booleans"]{Adding a base type}

Let’s make things a bit more interesting by introducing the potential for more
type errors. We add Booleans to the language. We add @term[true] and
@term[false], and @term[if] expressions for distinguishing between the two:
@;
@render-nonterminals[r:λ-ml t e v E]

There are two new reduction rules, for reducing @term[if] in the true case and
in the false case:
@;
@render-reduction-rules[r:->val if-true if-false]

The type rules assign type @term[bool] to both Boolean expressions. An @term[if]
expression types if the condition is a @term[bool] and if the branches have the
same type as each other:
@;
@render-judgment-rules[r:types true false if]

@exercise{Show that the term
 @term[(let f (λ x x) (if true (ap f true) (ap (ap f (λ y y)) false)))]
has no type.}

@subsection[#:tag "ml-let-poly"]{Introducing @tt{let} polymorphism}

By why not? The term reduces to a Boolean, so shouldn’t it have type
@term[bool]? It doesn’t because @term[f]
is used two different ways. When applied to @term[true], it needs to have
type @term[(-> bool bool)], but when applied to @term[(λ y y)] it needs to
have type @term[(-> (-> bool bool) (-> bool bool))] (because the result of that
application is applied to a @term[bool]).

However, if we were to reduce the @term[let], we would get
@term[(if true (ap (λ x x) true) (ap (ap (λ x x) (λ y y)) false))],
which types fine.

So this suggests a different way to type @term[(let x e_1 e_2)]: copy
@term[e_1] into each occurrence of @term[x] in @term[e_2]:
@;
@render-judgment-rules[r:types let-copy/wrong]
@;
with this rule, the example from the exercise types correctly. However, other
things that shouldn’t type also type. In particular, a term like
@term[(let f (λ x (ap x x)) true)] has type @term[bool], even though the
subterm @term[(λ x (ap x x))] has no type. To remedy this, we ensure that
@term[e_1] has a type, even though we don’t restrict it to have that particular
type in @term[e_2]:
@;
@render-judgment-rules[r:types let-copy]

This works! But it has two drawbacks:
@itemlist[
 @item{Now we are typechecking term @term[e_1] multiple times, once for each
  occurrence of @term[x] in @term[e_2]. We can actually construct a
  family of terms that grow exponentially as a result of this copying.}
 @item{In a real programming system, we want to be able to give a type
  to @term[x] because they often allow bindings with open scopes:
  @term[(let x e_1)] for the future. This only makes sense if we can
  say what type @term[x] has. This is essential for separate or
  incremental compilation.}
]

@section[#:tag "ml-type-schemes"]{Type schemes in @λ-ml}

In the exercise above, @term[x] is used at two different types:
@term[(-> bool bool)] and @term[(-> (-> bool bool) (-> bool bool))].
In fact, if we consider it carefully, it’s safe to use @term[x] on an
argument of any type @term[t], and we get that same @term[t] back.
So we could say that @term[x] has the @italic{type scheme}
@term[(-> a a)] for all types @term[a].

We will write type schemes with the universal quantifier to
indicate which type variables are free to be instantiated in the scheme:
@;
@render-nonterminals[r:λ-ml/no-bool σ]
@;
Note that types in @λ-ml (and real ML) do not contain @term[all] like System
F types do—@term[all] just happens in the front of type schemes.
(This is called a prenex type.) This is key to making type inference possible,
since we cannot in general infer System F types.

@section[#:tag "ml-statics"]{Statics}

For @λ-ml's statics, we allow type environments @term[Γ] to bind variables
to type schemes:
@;
@render-nonterminals[r:λ-ml/no-bool Γ]

@subsection[#:tag "ml-logical"]{The logical type system}

We first give a logical type system, which says which terms has a type but
is not very much help in finding the type. The four rules for the four
expression forms in our language are nearly the same as before; the only
difference is in rule @rulename[let-poly], allows the bound variable to have a
type scheme instead of a mere monomorphic type (“monotype”):
@;
@render-judgment-rules[r:types var abs app let-poly]
@;
On the other hand, notice that the domain type inferred for λ is still
required to be a monotype.

There are two initial rules, which are not syntax directed, but which are
used to instantiate type schemes to types and generalize types to type
schemes. To instantiate a type scheme, we can replace its bound variable
with any type whatsoever:
@;
@render-judgment-rules[r:types inst]

Finally, we can generalize any type variable that is not free in the
environment @term[Γ]:
@;
@render-judgment-rules[r:types gen]
@;
This is because any type variable that is not mentioned in @term[Γ] is
unconstrained, but type variables that are mentioned might have requirements
imposed on them.

@exercise{Derive a type for
 @term[(let f (λ x x) (if true (ap f true) (ap (ap f (λ y y)) false)))].}

@exercise{What types can you derive for @term[(λ x (λ y (ap x y)))]?
 What do they have in common? What type scheme instantiates to all of them?}

@subsection[#:tag "ml-syntax-directed"]{The syntax-directed type system}

The system presented above allows generalization and instantiation anywhere, but
in fact, these rules are only useful in certain places, because we do not allow
polymorphic type schemes as the domains of functions. The only
place that generalization is useful is when binding the right-hand side of a
@term[let], and instantiation is only useful when we lookup a variable with
a type scheme and want to use it. It's not necessary to apply the rules anywhere
else, so we can combine rule @term[var] with rule @term[inst] into a new rule
@rulename[var-inst]:
@;
@render-judgment-rules[r:types var-inst]

The rule uses a relation @term[>] for instantiating a type scheme into an
arbitrary monotype:
@;
@render-judgment-rules[r:> mono all]

Similarly, we combine rule @rulename[let-poly] with rule @rulename[gen]
to get rule @rulename[let-gen], which generalizes the right-hand side
of the @term[let]:
@;
@render-judgment-rules[r:types let-gen]

The metafunction gen simply generalizes the type into a type scheme with
the given bound variables:
@;
@render-metas[r:gen]

The syntax-directed type system presented in this section admits exactly the
same programs as the logical type system from the previous section. Unlike the
logical system, it tells us exactly when we need to apply instantiation and
generalization. But it still does not tell us what types to instantiate type
schemes to in rule @rulename[var-inst], and it does not tell us what type
to use for the domain in rule @term[abs]. To actually type terms, we will
need an algorithm.

@section[#:tag "ml-inference-algo"]{Type inference algorithm}

The type inference rules presented above yield many possible typings for terms.
For example, the identity function might have type @term[(-> a a)] or
@term[(-> bool bool)] or @term[(-> (-> bool a) (-> bool a))] and so on.
The most general type, however, is @term[(-> a a)], since all other terms
are instances of that. The algorithm presented in this section always finds
the most general type (if a typing exists).

@subsection[#:tag "ml-unification"]{Unification}

To perform type inference, we need a concept of a type substitution,
which substitutes some monotypes for type variables:
@;
@render-nonterminals[r:λ-ml/no-bool S]

@exercise{Give a type substitution @term[S] such that
 @term[(apply-subst S (-> a (-> a b)))] = @term[(-> bool (-> bool (-> c c)))]}

Type inference will hinge on the idea of unification: Given two types
@term[t_1] and @term[t_2], is there a substitution @term[S] that makes them
equal: @term[(apply-subst S t_1)] = @term[(apply-subst S t_2)]? We will use
this, for example, if we want to apply a function with type @term[(-> t_1 t)]
to argument of type @term[t_2]. Type variables represent unknown parts of the
types at question, and unification tells us if the types might be made, by
filling in missing information, the same.

The unification procedure takes two types and either produces the unifying
substitution, or fails. In particular, any variable unifies with itself,
producing the empty substitution:
@;
@render-judgment-rules[r:unify var-same]

A variable @term[a] unifies with any other type @term[t] by extending
the substitution to map @term[a] to @term[t], @italic{provided that
 @term[a] is not free in @term[t]}:
@;
@render-judgment-rules[r:unify var-left]
@;
(If @term[(∈ a (ftv t))] then they won't unify and we have a type error. This is
the only kind of type error in a system without base types.)

If a variable appears on the right, we swap it to the left and unify:
@;
@render-judgment-rules[r:unify bool-left arr-left]

Finally, two types unify if their domains unify and their codomains unify:
@;
@render-judgment-rules[r:unify arr]
@;
Note that after @term[(unify t_11 t_21 S)] produces a substitution @term[S],
we apply that substitution to @term[t_12] and @term[t_22] before unifying,
in order to propagate the information that we’ve collected. Further, the
result of unifying the arrow types is the composition of the substitutions
@term[S_1] and @term[S_2]. In general, when we work with substitutions, we
will see that we accumulate and compose them.

Unification has an interesting property: It finds the @italic{most general}
unifier for any pair of unifiable types. A substitution @term[S] is more
general than a substitution @term[S_1] if there exists a substitution @term[S_2]
such that @term[S_1] = @term[(compose-subst S_2 S)]. That is, if
@term[S_1] does more substitution than @term[S]. So suppose that @term[t_1]
and @term[t_2] are two types, and suppose that
@term[(apply-subst S_1 t_1)] = @term[(apply-subst S_1 t_2)]. Then the @term[S]
given by unifying @term[t_1] and @term[t_2] will be more general than (or
equal to) @term[S_1].

@subsection[#:tag "ml-algorithm-w"]{Algorithm W}

Now we are prepared to give the actual inference algorithm. It uses one
metafunction, inst, which takes a type scheme and instantiates its
bound variables with fresh type variables:
@;
@render-metas[r:inst]
@;
The inst metafunction is given a list of type variables to avoid.

Then we have the inference algorithm itself. The algorithm takes as parameters
a type environment and a term to type; if it succeeds, it returns both a type
for the term and a substitution making it so. Let's start with the simplest
rules.

To type check a Boolean, we return @term[bool] with the empty substitution:
@;
@render-judgment-rules[r:W true false]

To type check a variable, we look up the variable in the environment and
instantiate the resulting type scheme with fresh type variables:
@;
@render-judgment-rules[r:W var]

To type check a λ abstraction, we create a fresh type variable @term[a] to
use as its domain type, and we type check the body assuming that the formal
parameter has that type @term[a]:
@;
@render-judgment-rules[r:W abs]
@;
Note that while we “guess” a type variable @term[a] for the domain, it will
be refined (via unification) based on how it’s used in the body.

To type check an application is more involved than the other rules we have seen,
but the key operation is unifying the domain type of the operator with the type
of the operand. First, we infer types for @term[e_1] and @term[e_2], using
substitution @term[S_1] (the result of typing @term[e_1]) for typing @term[e_2].
Then, we get a fresh type variable @term[a] to stand for the result type of the
application. We unify the type of the operator, @term[(apply-subst S_2 t_1)]
with the type we need it to have, @term[(-> t_2 a)], yielding substitution
@term[S_3]. Then the composition of the three substitutions, along with result
type @term[(apply-subst S_3 a)], is our result:
@;
@render-judgment-rules[r:W app]
@;
Note again how the substitutions are threaded through: Substitutions must be
applied to any types or environments that existed before that substitution
was created.

For the @term[let] rule, we first infer a type for @term[e_1], and we
generalize that type with respect to the (updated-by-substitution) type
environment @term[(apply-subst S_1 Γ)]. Then we bind the resulting type
scheme in the environment for type checking @term[e_2]:
@render-judgment-rules[r:W let]

Finally, the rule for @term[if] works by first type checking its three
subterms, threading the substitutions through. Then it needs to unify the type
of @term[e_1] with @term[bool], and it needs to unify the types of @term[e_2]
and @term[e_3] with each other. Either of those is then the type of the result.
@;
@render-judgment-rules[r:W if]

@theorem[#:name "Soundness and completeness of W"]
@itemlist[
 @item{Soundness: If @term[(W • e S t)] then @term[(types • e t)].}
 @item{Completeness: If @term[(types • e t)] then @term[(W • e S t_1)] for
  some @term[t_1] that @term[t] is a substitution instance of.
  (That is, there is some substitution @term[S_1] such that
  @term[(apply-subst S_1 t_1)] = @term[t].)}
]

@section[#:tag "ml-constraints"]{Constraint-based type inference}

Algorithm W interleaves walking the term and unification. There’s another
approach based on @italic{constraints}, where we generate a constraint the
tells us what has to be true for a term to type, and then we solve the
constraint. This technique is important mostly because it allows us to
extend our type system in particular ways by adding new kinds of constraints.

Our language of constraints has the trivial true constraint
@term[⊤], the conjunction of two constraints @term[(∧ C C)], a constraint
that two types be equal @term[(= t t)], and a constraint @term[(∃ a C)] that
introduces a fresh type variable for the subconstraint @term[C]. Here is
the syntax of contraints:
@;
@render-nonterminals[r:λ-ml/no-bool C]

Then we can write a judgment that takes a constraint and, if possible, solves
it, producing a substitution:
@;
@render-judgment-rules[r:solve-constraint true and equals exists]

Now that we know how to solve contraints, it remains to generate them for a
given term. We do that with the metafunction @term[(generate Γ e t)],
which, given an environment, a term, and a type, generates the
constraints required for the typing judgment @term[(types Γ e t)] to hold:
@;
@render-metas[r:generate]

How can we use this to type a term if we don’t know its type to begin with?
Suppose we want to type a term @term[e] in the empty environment. Then we choose
a fresh type variable @term[a], generate the constraint that @term[e] has
type type, and solve the constraint, yielding a substitition:
@;
@centered[
 @term[(solve-constraint (generate • e a) S)]
]

Then we look up the type of @term[a] in the resulting substiution:
@term[(apply-subst S a)].

Note that for @term[let]-free programs, constraint generation is completely
separated from solving. However, when we encounter a @term[let], we still
interleave solving to get the generalized type of the let-bound variable.
