{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.State where

import Data.Tuple (swap)

import Control.Effect
import Control.Family.Algebraic
import qualified Control.Monad.Trans.State.Lazy as S

type Put s = Alg (Put' s)
data Put' s k where
  Put :: s -> k -> Put' s k
  deriving Functor

type Get s = Alg (Get' s)
data Get' s k where
  Get :: (s -> k) -> Get' s k
  deriving Functor

type State s = '[Put s, Get s]

put :: Member (Put s) sig => s -> Prog sig ()
put s = (Call . inj) (Alg (Put s (return ())))

get :: Member (Get s) sig => Prog sig s
get = injCall (Alg (Get return))

stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s] (S.StateT s m) x -> S.StateT s m x)
stateAlg _ eff
  | Just (Alg (Put s p)) <- prj eff =
      do S.put s
         return p
  | Just (Alg (Get p)) <- prj eff =
      do s <- S.get
         return (p s)

stateT :: s -> Handler [Put s, Get s] '[] '[S.StateT s] '[((,) s)]
stateT s = handler' (fmap swap . flip S.runStateT s) stateAlg

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
-- state_ :: s -> Handler [Put s, Get s] '[] '[]
-- state_ s = Handler $ Handler (\oalg -> fmap (RCNil . fst) . flip S.runStateT s) stateAlg

stateT_ :: s -> Handler [Put s, Get s] '[] '[S.StateT s] '[]
-- stateT_ s = Handler (\oalg -> fmap (RCNil . fst) . flip S.runStateT s) stateAlg
stateT_ s = handler (fmap fst . flip S.runStateT s) stateAlg

