-- Parallel effects

-- First developed in:
-- A framework for higher-order effects & handlers by
-- Birthe van den Berg and Tom Schrijvers

module Control.Family.Parallel where

import Data.Kind ( Type )
import Data.HFunctor

data Par (rho :: Type -> Type) (f :: Type -> Type) a where
    For :: (rho (f x)) -> (rho x -> a) -> Par rho f a

instance Functor rho => Functor (Par rho f) where
  fmap f (For iters c) = For iters (f . c)

instance Functor rho => (HFunctor (Par rho)) where
  hmap h (For iters c) = For (fmap h iters) c

