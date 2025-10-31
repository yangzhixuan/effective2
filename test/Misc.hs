{-# LANGUAGE TemplateHaskell, CPP, ViewPatterns #-}
module Main where

import Hedgehog
import Hedgehog.Main

import Control.Effect
import Control.Effect.State
import Control.Effect.Nondet
import Control.Effect.WithName
import Control.Effect.Internal.TH


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

example_Once :: Property
example_Once = property $
  handle (renameEff (Proxy @"a") (Proxy @Once) backtrack) p === [1, 2]
  where
    p :: Members '[Choose, Empty, "a" :@ Once] sig => Prog sig Int
    p = do x <- onceN "a" ((return 0) <|> (return 5))
           (return (x + 1)) <|> (return (x + 2))

data Flip_ k = Flip_ k Float k deriving Functor

$(makeAlgFrom ''Flip_)

-- >>> :t Main.flip
-- Main.flip :: Member Flip sig => Prog sig x -> Float -> Prog sig x -> Prog sig x
-- >>> :t Main.flipP
-- Main.flipP
--   :: Member (WithName name Flip) sig =>
--      Proxy name -> Prog sig x -> Float -> Prog sig x -> Prog sig x
-- >>> :t Main.flipN
-- Main.flipN
--   :: forall (name :: Symbol) ->
--      forall (sig :: [Effect]) x.
--      Member (WithName name Flip) sig =>
--      Prog sig x -> Float -> Prog sig x -> Prog sig x

-- >>> :t Main.Flip
-- Main.Flip :: Member (Alg Flip_) sigs => a -> Float -> a -> Effs sigs f a
-- >>> :kind! Main.Flip
-- Main.Flip :: (* -> *) -> * -> *
-- = Alg Flip_

main :: IO ()
main = defaultMain [checkParallel $$(discover)]
