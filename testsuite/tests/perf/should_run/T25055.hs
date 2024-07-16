{-# OPTIONS_GHC -Wall  #-}
-- based on https://byorgey.github.io/blog/posts/2024/06/21/cpih-product-divisors.html

module Main( main ) where

import Control.Monad
import Control.Monad.ST
import Data.Array.ST
import Data.Array.Unboxed
import Data.Foldable

smallest :: Int -> UArray Int Int
smallest maxN = runSTUArray $ do
  arr <- newGenArray (2,maxN) initA
  for_ [5, 7 .. maxN] $ \k -> do
      k' <- readArray arr k
      when (k == k') $ do
        for_ [k*k, k*(k+2) .. maxN] $ \oddMultipleOfK -> do
          modifyArray' arr oddMultipleOfK (min k)
  return arr
    where
      initA i
        | even i          = return 2
        | i `rem` 3 == 0  = return 3
        | otherwise       = return i

factor :: STUArray s Int Int -> Int -> Int -> ST s ()
-- With #25055 the program ran slow as it appear below, but
-- fast if you (a) comment out 'let p = smallest maxN ! m'
--             (b) un-comment the commented-out bindings for p and sm
factor countsArr maxN n  = go n
  where
    -- sm = smallest maxN

    go 1 = return ()
    go m = do
      -- let p = sm ! m
      let p = smallest maxN ! m
      modifyArray' countsArr p (+1)
      go (m `div` p)


counts :: Int -> [Int] ->  UArray Int Int
counts maxN ns  = runSTUArray $ do
  cs <- newArray (2,maxN) 0
  for_ ns (factor cs maxN)
  return cs

solve :: [Int] -> Int
solve = product . map (+ 1) . elems . counts 1000000

main :: IO ()
main =
  print $ solve [1..100]
