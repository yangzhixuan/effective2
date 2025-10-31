{-# LANGUAGE TemplateHaskell, CPP #-}
module Main where

import Hedgehog
import Hedgehog.Main

import Control.Effect
import Control.Effect.State
import Control.Effect.IO


type E = ["a" :@ Put Int, "a" :@ Get Int, "b" :@ Put Int, "b" :@ Get Int]

a :: Proxy "a"
a = Proxy

b :: Proxy "b"
b = Proxy

fib :: Int -> Int ! E
fib 0 = getP b
fib n = do sA <- getP a
           sB <- getP b
           putP b (sA + sB)
           putP a (sB :: Int)
           fib (n - 1)

prop_fib :: Property
prop_fib = property $ p === 21 where
  p :: Int
  p = handle
        (renameEffs a (state_ (0 :: Int))
          |> renameEffs b (state_ (1 :: Int)))
        (fib 7)

#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
-- A version of @fib@ that uses @getN@/@putN@.
fib' :: Int -> Int ! E
fib' 0 = getN "b"
fib' n = do sA <- getN "a"
            sB <- getN "b"
            putN "b" (sA + sB)
            putN "a" (sB :: Int)
            fib' (n - 1)

prop_fib' :: Property
prop_fib' = property $ p === 21 where
  p :: Int
  p = handle
        (renameEffs a (state_ (0 :: Int))
          |> renameEffs b (state_ (1 :: Int)))
        (fib' 7)
#endif


main :: IO ()
main = defaultMain [checkParallel $$(discover)]