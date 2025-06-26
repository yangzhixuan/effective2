{-|
Module      : Control.Effect.Nondet
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

module Control.Effect.Nondet
  ( Choose
  , Choose_(Choose)
  , Empty
  , Empty_(Empty)
  , (<|>)
  , empty
  , ListT (..)
  , stop
  , or
  , select
  , selects
  , nondet
  , Once
  , Once_ (..)
  , once
  , list
  , backtrackAlg
  , backtrackOnceAlg
  , backtrack
  ) where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative

import Control.Monad.Trans.List

-- | `stop` represents a computation that immediately fails.
-- It uses the t`Empty` effect to signal failure.
{-# INLINE stop #-}
stop :: Members '[Empty] sig => Prog sig a
stop  = call (Alg Empty)

-- | `or` represents a nondeterministic choice between two computations.
-- It uses the t`Choose` effect to combine the results of the two computations.
{-# INLINE or #-}
or :: Members '[Choose] sig => Prog sig a -> Prog sig a -> Prog sig a
or x y = call (Scp (Choose x y))

-- | `select` nondeterministically selects an element from a list.
-- If the list is empty, the computation fails.
select :: Members [Choose, Empty] sig => [a] -> Prog sig a
select = foldr (or . return) stop

-- | `selects` generates all permutations of a list, returning each element
-- along with the remaining elements of the list.
selects :: [a] -> (a, [a]) ! [Choose, Empty]
selects []      =  empty
selects (x:xs)  =  return (x, xs)  <|>  do  (y, ys) <- selects xs
                                            return (y, x:ys)

-- | The `nondet` handler transforms nondeterministic effects t`Empty` and t`Choose`
-- into the t`ListT` monad transformer, which collects all possible results.
{-# INLINE nondet #-}
nondet :: Handler [Empty, Choose] '[] '[ListT] '[[]]
nondet = handler' runListT' (getAT alternativeAT)

-- | Signature for delimiting the scope of nondeterminism to `once`
type Once = Scp Once_
-- | Underlying signature for delimiting the scope of nondeterminism to `once`
data Once_ a where
  Once :: a -> Once_ a
  deriving Functor

-- | `once` restricts a computation to return at most one result.
once
  :: Member Once sig => Prog sig a -> Prog sig a
once p = call (Scp (Once p))

backtrackOnceAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Once] (ListT m) x -> ListT m x)
backtrackOnceAlg oalg op
  | Just (Scp (Once p)) <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))

-- | `backtrackAlg'` combines the semantics of alternative and backtracking
-- for the t`Empty`, t`Choose`, and t`Once` effects.
backtrackAlg
  :: Monad m => (forall x. Effs '[] m x -> m x)
  -> (forall x. Effs [Empty, Choose, Once] (ListT m) x -> ListT m x)
backtrackAlg oalg = (getAT alternativeAT oalg) # backtrackOnceAlg oalg

backtrackAT :: AlgTrans [Empty, Choose, Once] '[] '[ListT] Monad
backtrackAT = AlgTrans backtrackAlg

-- | `backtrack` is a handler that transforms nondeterministic effects
-- t`Empty`, t`Choose`, and t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrack :: Handler [Empty, Choose, Once] '[] '[ListT] '[[]]
backtrack = handler' runListT' backtrackAlg