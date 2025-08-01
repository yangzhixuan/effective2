{-|
Module      : Control.Effect.State.Type
Description : Types for state effect
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.State.Type where

import Control.Effect
import Control.Effect.Family.Algebraic

-- | Signature for putting a value into the state.
type Put s = Alg (Put_ s)
-- | Underlying signature for putting a value into the state.
data Put_ s k where
  Put_ :: s -> k -> Put_ s k
  deriving Functor

pattern Put :: Member (Put s) effs => s -> k -> Effs effs m k
pattern Put s k <- (prj -> Just (Alg (Put_ s k)))
  where Put s k = inj (Alg (Put_ s k))

-- | Syntax for putting a value into the state.
{-# INLINE put #-}
put :: Member (Put s) sig => s -> Prog sig ()
put s = call (Alg (Put_ s ()))

-- | Signature for getting a value from the state.
type Get s = Alg (Get_ s)

-- | Underlying signature for getting a value from the state.
newtype Get_ s k where
  Get_ :: (s -> k) -> Get_ s k
  deriving Functor

pattern Get :: Member (Get s) effs => (s -> k) -> Effs effs m k
pattern Get k <- (prj -> Just (Alg (Get_ k)))
  where Get k = inj (Alg (Get_ k))

-- | Syntax for getting a value from the state.
{-# INLINE get #-}
get :: Member (Get s) sig => Prog sig s
get = call (Alg (Get_ id))
