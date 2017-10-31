{-# LANGUAGE
      RankNTypes,
      ScopedTypeVariables,
      TypeApplications
  #-}
module Church where

type CBool = forall a. a -> a -> a

ctrue, cfalse :: CBool
ctrue = \t f -> t
cfalse = \t f -> f

cnot :: CBool -> CBool
cnot b = b cfalse ctrue

cand, cor, cxor :: CBool -> CBool -> CBool
cand b1 b2 = b1 b2 cfalse
cor b1 b2 = b1 ctrue b2
cxor b1 b2 = b1 (cnot b2) b2

reify_cbool :: CBool -> Bool
reify_cbool b = b True False

type CPair a b = forall r. (a -> b -> r) -> r

mkPair :: a -> b -> CPair a b
mkPair a b = \k -> k a b

cfst :: CPair a b -> a
csnd :: CPair a b -> b

cfst cpair = cpair (\a b -> a)
csnd cpair = cpair (\a b -> b)

reify_cpair :: CPair a b -> (a, b)
reify_cpair cpair = cpair (\a b -> (a, b))

type CNat = forall a. (a -> a) -> a -> a

c0 :: CNat
c0  = \f x -> x

c1, c2, c3 :: CNat
c1  = \f x -> f x
c2  = \f x -> f (f x)
c3  = \f x -> f (f (f x))

csucc :: CNat -> CNat
csucc n = \f x -> n f (f x)

c4, c5, c6 :: CNat
c4 = csucc c3
c5 = csucc c4
c6 = csucc c5

-- Requires impredicative polymorphism:
-- cpred :: CNat -> CNat
-- cpred cn = cfst ((cn @ (CPair CNat CNat))
--                    (\cpair -> mkPair (csnd cpair) (csucc (csnd cpair)))
--                     (mkPair c0 c0))

reify_cnat :: CNat -> Int
reify_cnat cn = cn (+ 1) 0

type CList a = forall b. b -> (a -> b -> b) -> b

cnil :: CList a
cnil z f = z

ccons :: a -> CList a -> CList a
ccons x xs = \z f -> f x (xs z f)


