{-# LANGUAGE DataKinds #-}

module Control.Effect.State.Type where

import Control.Effect
import Control.Family.Algebraic

type Put s = Alg (Put' s)
data Put' s k where
  Put :: s -> k -> Put' s k
  deriving Functor

type Get s = Alg (Get' s)
newtype Get' s k where
  Get :: (s -> k) -> Get' s k
  deriving Functor

type State s = '[Put s, Get s]

{-# INLINE put #-}
put :: Member (Put s) sig => s -> Prog sig ()
put s = injCall (Alg (Put s (return ())))

{-# INLINE get #-}
get :: Member (Get s) sig => Prog sig s
get = injCall (Alg (Get return))
