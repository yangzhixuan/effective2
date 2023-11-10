{-# LANGUAGE QuantifiedConstraints #-}

module Data.HFunctor where

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Identity

import Data.Kind ( Type )

class (forall f . Functor f => Functor (h f)) => HFunctor (h :: (Type -> Type) -> (Type -> Type)) where
  hmap :: (Functor f, Functor g) => (forall x . f x -> g x) -> (h f) x -> (h g) x

instance HFunctor MaybeT where
  hmap h (MaybeT mx) = MaybeT (h mx)

instance HFunctor IdentityT where
  hmap h (IdentityT x) = IdentityT (h x)
