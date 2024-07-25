{-# LANGUAGE DataKinds #-}

module Control.Effect.State.Lazy
  ( module Control.Effect.State.Lazy
  , module Control.Effect.State.Type
  ) where

import Control.Effect
import Control.Effect.State.Type
import Control.Effect.Algebraic

import qualified Control.Monad.Trans.State.Lazy as Lazy

state :: s -> Handler [Put s, Get s] '[] (Lazy.StateT s) ((,) s)
state s = handler (fmap (\ ~(x, y) -> (y, x)) . flip Lazy.runStateT s) stateAlg

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
-- state_ :: s -> Handler [Put s, Get s] IdentityT Identity
-- state_ s = Handler $ Handler (\oalg -> fmap (RCNil . fst) . flip S.runStateT s) stateAlg
state_ :: s -> Handler [Put s, Get s] '[] (Lazy.StateT s) Identity
-- state_ s = Handler (\oalg -> fmap (RCNil . fst) . flip S.runStateT s) stateAlg
state_ s = handler (fmap Identity . flip Lazy.evalStateT s) stateAlg

stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s] (Lazy.StateT s m) x -> Lazy.StateT s m x)
stateAlg _ op
  | Just (Alg (Put s p)) <- prj op =
      do Lazy.put s
         return p
  | Just (Alg (Get p)) <- prj op =
      do s <- Lazy.get
         return (p s)
