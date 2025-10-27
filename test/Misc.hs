{-# LANGUAGE TemplateHaskell #-}
module Main where

import Hedgehog
import Hedgehog.Main

import Control.Effect
import Control.Effect.State
import Control.Effect.WithName
import Control.Effect.IO


putN :: forall n. Int -> () ! '[n :@ Put Int]
putN n = callWithNameAlg @n (Put_ n ())

getN :: forall n. Int ! '[n :@ Get Int]
getN = callWithNameAlg @n (Get_ id)

type E = ["a" :@ Put Int, "a" :@ Get Int, "b" :@ Put Int, "b" :@ Get Int]

fib :: Int -> Int ! E
fib 0 = getN @"b"
fib n = do sA <- getN @"a"
           sB <- getN @"b"
           putN @"b" (sA + sB)
           putN @"a" sB
           fib (n-1)

prop_fib :: Property
prop_fib = property $ p === 21 where
  p :: Int
  p = handle
        (renameEffs (Proxy @"a") (state_ (0 :: Int))
          |> renameEffs (Proxy @"b") (state_ (1 :: Int)))
        (fib 7)


main :: IO ()
main = defaultMain [checkParallel $$(discover)]
