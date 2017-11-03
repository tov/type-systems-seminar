#lang scribble/base

@(require (prefix-in r: "redex/poly.rkt")
          (prefix-in stlc: "redex/stlc.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λ-2)
@define[λ-2]{@langname[λ-2]}

@title{The polymorphic lambda calculus @λ-2}

Suppose we want to write the composition function in the simply-typed
lambda calculus. What does it look like? Well, it depends on the types
of the functions. We can compose two @term[(-> nat nat)] functions with this:
@;
@centered[
 (parameterize ([default-language stlc:stlc])
   @term[(λ x_1 (-> nat nat) (λ x_2 (-> nat nat) (λ y nat (ap x_1 (ap x_2 y)))))])
]
@;
But if the functions have different types, we will need to define a
different composition function. This is awkward!

Polymorphism lets us write one composition function that works for any types.
We introduce type variables @term[a_i] and abstract over them with @term[Lam]:
@;
@centered[
    @term[(Lam a_1 (Lam a_2 (Lam a_3 (lam x_1 (-> a_2 a_3) (lam x_2 (-> a_1 a_2) (lam y a_1 (app x_1 (app x_2 y))))))))]
]
@;
We model polymorphism with @λ-2, also known as System F.

@section[#:tag "system-f-syntax"]{Syntax}

@render-nonterminals[r:λ-2 t e]

@section[#:tag "system-f-dynamics"]{Dynamic semantics}

To give the dynamic semantics of @λ-2, we first define values and
the evaluation contexts:

@render-nonterminals[r:λ-2 E v]

Then the reduction relation has two rules, one for value abstraction
applications, and one for type abstraction applications:

@render-reduction-rules[r:->val β-val inst]

The dynamic semantics of @poly is given by the evaluation function @emph{eval}:

@centered[
@tabular[
 #:sep @hspace[1]
 #:column-properties '(left left)          
 (list (list @list{eval(@term[e]) = @term[v]}
             @list{if @term[(-->* e v)]}))
]
]

As defined, @emph{eval} could be partial, as with STLC, it is total on
well typed terms.

@section[#:tag "system-f-statics"]{Static semantics}

To give the static semantics of @λ-2, we have both type variable
environments (which tell us which type variables are in scope) and
typing environments (which map variables to their types):

@render-nonterminals[r:λ-2 Δ Γ]

The main typing judgment relies on two auxiliary judgments. The
first tells us whether a type is well formed (which for this language just
means closed):

@render-judgment-rules[r:kinds var var arr all]

A typing environment is well formed when all the types in it are well formed:

@render-judgment-rules[r:kinds/env nil cons]

Finally, we give the typing judgments for @|λ-2|:

@render-judgment-rules[r:types var app abs t-abs t-app]

Strictly speaking, every Δ and every type well-formedness premiss can
go away and it all still works, with type variables acting like constants,
but I like knowing where my free type variables are.

@section[#:tag "system-f-church"]{Church data}

@λ-2, made of lambdas big and small, may seem to lack much in the way
of data, but in fact it is very rich. Alonzo Church showed how to represent
natural numbers and datatypes in the untyped lambda calculus. STLC is too
weak for those encodings to be meaningful, but they work beautifully in
@|λ-2|.

@subsection[#:tag "system-f-cnats"]{Natural numbers}

The natural numbers can be defined as functions that iterate a function.
In particular, define type @term[Nat] to be
@term[(all a (-> (-> a a) (-> a a)))], with

@itemlist[
 @item{c0 = @term[(Lam a (lam f (-> a a) (lam x a x)))],}
 @item{c1 = @term[(Lam a (lam f (-> a a) (lam x a (app f x))))],}
 @item{c2 = @term[(Lam a (lam f (-> a a) (lam x a (app f (app f x)))))],}
 @item{and in general, c@emph{n} as the function that for any type @term[a],
       iterates an @term[(-> a a)] function @emph{n} times.}
]

@exercise{Define the successor function @term[succ] of type
 @term[(-> Nat Nat)].}

@exercise{Define addition, multiplication, and exponentiation.}

@exercise[#:name "hard"]{Define the predecessor function.}

Once we have predecessor we can define subtraction, equality, less-than,
and more, but we need a bit more technology before we can define predecessor.

@subsection[#:tag "system-f-cbools"]{Booleans}

The Booleans can be defined as their own elimination rule. In particular,
let type @term[Bool] = @term[(all a (-> a (-> a a)))]. Then define:

@itemlist[
 @item{tru = @term[(Lam a (lam x a (lam y a x)))], and}
 @item{fls = @term[(Lam a (lam x a (lam y a y)))].}
]

There’s no need for if-then-else—just apply the Boolean.

@exercise{Define @emph{not}, @emph{and}, and @emph{or}.}

@exercise{Define @term[(types* zero? (-> Nat Bool))].}

@subsection[#:tag "system-f-cprods"]{Products}

In general, we can represent datatypes by their elimination principles.
For example, we represent the product @term[(* t_1 t_2)] as
a function of type @term[(all a (-> t_1 (-> t_2 a)) a)]. That is, a pair of
a @term[t_1] and a @term[t_2] is a function that, for any type @term[a], you
can give it a function that turns a @term[t_1] and @term[t_2] into an @term[a],
and it gives back that @term[a].

The pair value @term[(pair v_1 v_2)] of type @term[(* t_1 t_2)]
is represented as
@term[(Lam a (lam y (-> t_1 (-> t_2 a)) ((y v_1) v_2)))].

@exercise{How can we write the selectors fst and snd?}

@exercise{Now predecessor becomes possible. The idea is to apply the Nat to
 count upward, but using a pair to institute a delay.}

@exercise{Define the recursor from our STLC extension.}

@subsection[#:tag "system-f-csums"]{Sums}

We can represent the sum type @term[(+ t_1 t_2)] as its elimination rule
@term[(all a (-> (-> t_1 a) (-> (-> t_2 a) a)))]. (Write that out in infix.)

@exercise{How can we construct sum values? How do we use them?}

@subsection[#:tag "system-f-lists"]{Lists}

We can represent a list using its elimination rule, in particular, the type of
its fold. Let @term[(List t)] =
@term[(all a (-> a (-> (-> t (-> a a)) a)))].

@exercise{Define cons.}

@exercise{Define @term[(types* sum (-> (List Nat) Nat))].}

@exercise{Define empty?, first, and rest.}

@subsection[#:tag "system-f-existentials"]{Existentials}

We can encode existential types in @|λ-2|. An existential
type lets us hide part of the representation of a type, and then safely use
it without revealing the representation.

Define @term[(ex a t)] to be @term[(all b (-> (all a (-> t b)) b))].

To create an existential, we must have a value @term[v_rep] that has some
actual type @term[t_act], but we wish to view as type @term[(ex a t)].
There must be some type @term[t_rep] such that @term[(substitute t a t_rep)]
= @term[t_act]. Then to create the existential, we write:

@centered[
 @term[(Lam b (lam y (all a (-> t b)) (app (App y t_rep) v_rep)))]
]

To use the existential, apply it!

For example, suppose we want to create a value of type
@term[(ex a (* a (* (-> a a) (-> a Nat))))] that lets us work abstractly with
the naturals. (In particular, we represent a triple containing zero of abstract
type, the successor function of abstract type, and a projection that reveals
the underlying natural.) We could pack that up as:

@centered{
 Counter =
   @term[(Lam b (lam y (all a (-> (* a (* (-> a a) (-> a Nat))) b))
                  (app (App (y (* Nat (* (-> Nat Nat) (-> Nat Nat)))))
                       (pair c0 (pair succ (lam x Nat x))))))]
}

Then to count to 2, we might write:

@centered[
 @term[(app (App Counter Nat)
            (Lam a (lam counter (* a (* (-> a a) (-> a Nat)))
                     ((snd (snd counter))
                      ((fst (snd counter))
                       ((fst (snd counter))
                        (fst counter)))))))]
]

This is the basis of abstract types as the appear in module and object systems.
Of course, it gets a bit easier to read if we add record types and make
existentials primitive or, better yet, hidden.

@exercise{Add existentials to @λ-2 without encoding as universals. In
 particular, you will need forms for packing and unpacking whose statics and
 dynamics agree with the encoding above.}

@exercise{Proof type safety and/or normalization for @|λ-2|.}

Consider this alternate definition of Counter:

@centered{
 Counter =
   @term[(Lam b (lam y (all a (-> (* a (* (-> a a) (-> a Nat))) b))
                  (app (App (y (* Nat (* (-> Nat Nat) (-> Nat Nat)))))
                       (pair c1 (pair succ pred)))))]
}

It should be indistinguishable from the original definition in all contexts.
Can we prove it?

                              
