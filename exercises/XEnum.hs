{-# LANGUAGE ScopedTypeVariables #-}

module XEnum where

import Test.QuickCheck
import Numeric.Natural

class XEnum a where
  into  :: a -> Natural
  outof :: Natural -> a

instance XEnum Natural where
  into n = n
  outof n = n

instance XEnum Integer where
  into x
    | x >= 0 = 2 * (fromInteger x)
    | x <  0 = 2 * (fromInteger (-x)) - 1
  outof x
    | x `mod` 2 == 0 = toInteger (div x 2)
    | x `mod` 2 == 1 = - (toInteger (div x 2)) - 1
    
instance (XEnum a , XEnum b) => XEnum (Either a b) where
  into (Left x)  = (into x) * 2
  into (Right x) = (into x) * 2 + 1
  outof x
    | even x    = Left  (outof (x `div` 2))
    | otherwise = Right (outof (x `div` 2))

{- function courtesy of https://stackoverflow.com/users/2124786/enrique via
   https://stackoverflow.com/questions/19965149/integer-square-root-function-in-haskell
 -}
squareRoot :: Natural -> Natural
squareRoot n
   | n > 0    = babylon n
   | n == 0   = 0
   where
   babylon a   | a > b  = babylon b
               | True   = a
      where b  = quot (a + quot n a) 2

instance (XEnum a, XEnum b) => XEnum (a, b) where
  into (a , b) = if x < y
                 then y*y+x
                 else x*x+x+y
    where x = into a
          y = into b

  outof z = if r < flroot
            then (outof r, outof flroot)
            else (outof flroot, outof (r - flroot))
   where flroot = squareRoot z
         r = z - flroot*flroot

data NElist a =
    NELast a
  | NECons (a , NElist a) deriving (Eq, Show)

toNElist :: a -> [a] -> NElist a
toNElist a [] = NELast a
toNElist a (x : xs) = NECons (a , toNElist x xs)

fromNElist :: NElist a -> [a]
fromNElist (NELast a) = [a]
fromNElist (NECons (a , b)) = a : fromNElist b

instance Arbitrary a => Arbitrary (NElist a) where
  arbitrary = do
    hd <- arbitrary
    tl <- arbitrary
    return (toNElist hd tl)

instance XEnum a => XEnum (NElist a) where
  into (NELast a) =       into (Left a             :: Either a (a , Natural))
  into (NECons (a , b)) = into (Right (a , into b) :: Either a (a , Natural))

  outof n = f (outof n) where

    f :: Either a (a , Natural) -> NElist a
    f (Left a) = NELast a
    f (Right (a, n)) = NECons (a , outof n)

instance XEnum a => XEnum [a] where
  into []       = 0
  into (x : xs) = (into (toNElist x xs)) + 1 where

  outof 0 = []
  outof n = fromNElist (outof (n-1)) where

prop_inout :: (Eq a, XEnum a) => a -> Bool
prop_inout x = outof (into x) == x

main :: IO ()
main = do
    _ <- quickCheck (prop_inout :: Integer -> Bool)
    _ <- quickCheck (prop_inout :: Either Integer Natural -> Bool)
    _ <- quickCheck (prop_inout :: (Integer , Integer) -> Bool)
    _ <- quickCheck (prop_inout :: Either Integer (Integer , Integer) -> Bool)
    _ <- print ((map outof [0..100]) :: [[Natural]])
{- these two run into a performance problem -}
{- _ <- quickCheck (prop_inout :: NElist Integer -> Bool) -}
{- _ <- quickCheck (prop_inout :: [Integer] -> Bool) -}
    return ()
