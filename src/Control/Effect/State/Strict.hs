{-# LANGUAGE DataKinds #-}

module Control.Effect.State.Strict
  ( module Control.Effect.State.Strict
  , module Control.Effect.State.Type
  ) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.State.Type

import qualified Control.Monad.Trans.State.Strict as Strict
import Data.Tuple (swap)

state :: s -> Handler [Put s, Get s] '[] (Strict.StateT s) ((,) s)
state s = handler (fmap swap . flip Strict.runStateT s) stateAlg

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
-- state_ :: s -> Handler [Put s, Get s] IdentityT Identity
-- state_ s = Handler $ Handler (\oalg -> fmap (RCNil . fst) . flip S.runStateT s) stateAlg
state_ :: s -> Handler [Put s, Get s] '[] (Strict.StateT s) Identity
-- state_ s = Handler (\oalg -> fmap (RCNil . fst) . flip S.runStateT s) stateAlg
state_ s = handler (fmap Identity . flip Strict.evalStateT s) stateAlg

stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s] (Strict.StateT s m) x -> Strict.StateT s m x)
stateAlg _ op
  | Just (Alg (Put s p)) <- prj op =
      do Strict.put s
         return p
  | Just (Alg (Get p)) <- prj op =
      do s <- Strict.get
         return (p s)
