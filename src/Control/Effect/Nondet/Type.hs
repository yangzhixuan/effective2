{-|
Module      : Control.Effect.Nondet.Type
Description : Effects for nondeterministic computations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides effects and handlers for nondeterministic computations,
including choice and failure.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Nondet.Type where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative

type Nondet = Alg Choose_

pattern Nondet :: Member Nondet effs => k -> k -> Effs effs m k
pattern Nondet x y <- (prj -> Just (Alg (Choose_ x y)))

-- | Signature for delimiting the scope of nondeterminism to `once`
type Once = Scp Once_
-- | Underlying signature for delimiting the scope of nondeterminism to `once`
data Once_ a where
  Once_ :: a -> Once_ a
  deriving Functor

pattern Once :: Member Once effs => m k -> Effs effs m k
pattern Once p <- (prj -> Just (Scp (Once_ p)))

-- | `once` restricts a computation to return at most one result.
once
  :: Member Once sig => Prog sig a -> Prog sig a
once p = call (Scp (Once_ p))

-- | Execute a computation within a t`Once` scope using a monadic handler.
onceM :: (Monad m, Member Once sig)
  => (forall a . Effs sig m a -> m a) -> m a -> m a
onceM alg p = (alg . inj) (Scp (Once_ p))

-- | `select` nondeterministically selects an element from a list.
-- If the list is empty, the computation fails.
select :: [a] -> a ! [Choose, Empty]
select xs = foldr ((<|>) . return) empty xs

-- | `selects` generates all permutations of a list, returning each element
-- along with the remaining elements of the list.
selects :: [a] -> (a, [a]) ! [Choose, Empty]
selects []      =  empty
selects (x:xs)  =  return (x, xs)  <|> do  (y, ys) <- selects xs
                                           return (y, x:ys)
