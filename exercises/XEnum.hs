{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Test.QuickCheck
import Numeric.Natural

instance Arbitrary Natural where
  arbitrary = arbitrarySizedNatural
  shrink    = shrinkIntegral

class XEnum a where
  into  :: a -> Natural
  outof :: Natural -> a

instance XEnum Natural where
  into n = n
  outof n = n

instance XEnum Integer where
  into x = error "not implemented"
  outof n = error "not implemented"

instance (XEnum a , XEnum b) => XEnum (Either a b) where
  into (Left x)  = error "not implemented"
  into (Right x) = error "not implemented"
  outof n = error "not implemented"

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

prop_sqrt :: Natural -> Bool
prop_sqrt n = rt * rt <= n && (rt + 1) * (rt + 1) > n
  where rt = squareRoot n

instance (XEnum a , XEnum b) => XEnum (a , b) where
  into (a , b) = error "not implemented"
  outof n = error "not implemented"

instance XEnum a => XEnum [a] where
  into l = error "not implemented"
  outof n = error "not implemented"

prop_inout :: (Eq a, XEnum a) => a -> Bool
prop_inout x = outof (into x) == x

main :: IO ()
main = do
    _ <- quickCheck prop_sqrt
    _ <- quickCheck (prop_inout :: Natural -> Bool)
    _ <- quickCheck (prop_inout :: Integer -> Bool)
{-    _ <- quickCheck (prop_inout :: Either Integer Natural -> Bool) -}
{-    _ <- quickCheck (prop_inout :: (Integer, Integer) -> Bool) -}
{-    _ <- quickCheck (prop_inout :: Either Integer (Integer, Integer) -> Bool) -}
{-    _ <- print (map outof [0..100] :: [[Natural]]) -}
{- these two run into a performance problem -}
{- _ <- quickCheck (prop_inout :: NElist Integer -> Bool) -}
{- _ <- quickCheck (prop_inout :: [Integer] -> Bool) -}
    return ()
