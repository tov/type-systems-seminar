module _ where

{-

One amazing thing about the calculus of constructions is that it can
form the basis for all of mathematics[*].  It can be pretty abstract
and hard to see that when you work directly with the calculus, but
there are various programming languages built on top of it that
emphasize that kind of thing.

Lets see one: agda. (Technically this isn't build on CoC, it is build
on another thing that is a hybrid of CoC with something else. We won't
care or be able to tell, really.)

[*]: constructive mathematics, really

-}

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong ; trans)

{- 

First, we can define the natural numbers. This is just a standard
define-type, but in Agda notation. It says that there are two
constructors "zero" and "S", and that "zero" takes no arguments to
make a Nat, and "S" takes one argument to make a Nat. In other words,
these are unary numbers.

-}

data Nat : Set where
  zero : Nat
  S : Nat -> Nat


{- lets define addition (append! :) -}
add : Nat -> Nat -> Nat
add zero y = y
add (S x) y = S (add x y)

{- Let prove things about the functions we've defined. One thing
   that's true is that x+y = y+x. Lets state that property:

addcomm : ∀ a b -> add a b ≡ add b a
addcomm a b = ?

In agda, you state a property by writing down its
type and then you have to define an expression that
has that type in order to prove it. In this case, we
have defined it as simply "?", which means "I know
I'm not done, here is a place I'll work more later".

In order to prove this, we need to know how to prove equalities. There
are four ways that we'll use today:

  refl : a ≡ a

  sym : a ≡ b -> b ≡ a

  trans : i ≡ j -> j ≡ k -> i ≡ k

  cong S : a ≡ b -> S a ≡ S b
    (we can use "cong" with other arguments, too, later)

  Lets prove this by cases on `a` and `b`; there are
  four cases; lets look at them each one at a time:

  .... it will turn out we'll need a helper lemma, addSS.

-}

addSS : ∀ a b -> add a (S b) ≡ S (add a b)
addSS zero b = refl
addSS (S a) b = cong S (addSS a b)

addcomm : ∀ a b -> add a b ≡ add b a
addcomm zero zero = refl
addcomm zero (S b) = cong S (addcomm zero b)
addcomm (S a) zero = cong S (addcomm a zero)
addcomm (S a) (S b) =
  cong S (trans (addSS a b) (trans (cong S (addcomm a b)) (sym (addSS b a))))

{-

Using agda we can also define data structure that don't just represent
ordinary data like numbers, but we can define data structures that
represent proofs -- proofs are just trees, after all, right?

Here is a definition of a data structure that represents evenness:

-}

data Even : Nat -> Set where
  ZeroIsEven : Even zero
  AddingTwo : ∀ n -> Even n -> Even (S (S n))

{-

Just like the definition of `nat`s, this starts with `data`, which
means we're defining some kind of trees. In this case, however, we're
defining the trees parameterized by a "nat". And we only allow certain
nats to show up there, because we allow only the constructors for our
trees as defined below.

In this case, we're saying that "ZeroIsEven" is a constructor whose
type is "Even zero". Or, in other words, "ZeroIsEven" is the proof
that zero is even. If we wanted to prove another number is even, 
we'd have to involve the other constructor. For example, if we write
this down:

  AddingTwo zero ZeroIsEven

then we're building a tree with the "AddingTwo" interior node, which
needs two arguments, a nat and a proof that that nat is even, and then
what we get is a proof that the next even number is, in fact even.

Here's what we write to get agda to check that for us.

-}

twoiseven : Even (S (S zero))
twoiseven = AddingTwo zero ZeroIsEven 


{-

Since this tree is, um, a tree, we can write functions that consume
it. Since this tree is a proof, those functions are also proofs! A
function as a proof is an implication (maybe you could have guessed
that from the arrow?

-}

sumofevens : ∀ n m -> Even n -> Even m -> Even (add n m)
sumofevens .zero m ZeroIsEven evenm = evenm
sumofevens .(S (S n)) m (AddingTwo n evenn) evenm
  = AddingTwo (add n m) (sumofevens n m evenn evenm) 


{- ... append again ... -}


{-

 there are two different, both natural ways to define less than on
 natural numbers. One where the "base case" is that zero is less than
 everything and the other is where every number is less than
 itself. Lets set them up and prove they are equivalent to each other

-}

data le1 : Nat -> Nat -> Set where
  ZeroLeAll : ∀ n -> le1 zero n
  SuccLe : ∀ n m -> le1 n m -> le1 (S n) (S m)

data le2 : Nat -> Nat -> Set where
  EqIsLe : ∀ n -> le2 n n
  SuccR : ∀ n m -> le2 n m -> le2 n (S m)

zerole2m : ∀ m -> le2 zero m
zerole2m zero = EqIsLe zero
zerole2m (S m) = SuccR zero m (zerole2m m)

SuccLe2 : ∀ n m -> le2 n m -> le2 (S n) (S m)
SuccLe2 n .n (EqIsLe .n) = EqIsLe (S n)
SuccLe2 n .(S m) (SuccR .n m le2nm) = SuccR (S n) (S m) (SuccLe2 n m le2nm)

le1->le2 : ∀ n m -> le1 n m -> le2 n m
le1->le2 .zero m (ZeroLeAll .m) = zerole2m m
le1->le2 .(S n) .(S m) (SuccLe n m le1nm) = SuccLe2 n m (le1->le2 n m le1nm)

EqIsLe1 : ∀ n -> le1 n n
EqIsLe1 zero = ZeroLeAll zero
EqIsLe1 (S n) = SuccLe n n (EqIsLe1 n)

SuccRLe1 : ∀ n m -> le1 n m -> le1 n (S m)
SuccRLe1 .zero m (ZeroLeAll .m) = ZeroLeAll (S m)
SuccRLe1 .(S n) .(S m) (SuccLe n m le1nm) = SuccLe n (S m) (SuccRLe1 n m le1nm)

le2->le1 : ∀ n m -> le2 n m -> le1 n m
le2->le1 n .n (EqIsLe .n) = EqIsLe1 n
le2->le1 n .(S m) (SuccR .n m le2nm) = SuccRLe1 n m (le2->le1 n m le2nm)
