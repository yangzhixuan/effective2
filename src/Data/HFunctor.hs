{-# LANGUAGE QuantifiedConstraints #-}

module Data.HFunctor where

import Data.Kind

class (forall f . Functor f => Functor (h f)) => HFunctor (h :: (Type -> Type) -> (Type -> Type)) where
  hmap :: (Functor f, Functor g) => (forall x . f x -> g x) -> (h f) x -> (h g) x

