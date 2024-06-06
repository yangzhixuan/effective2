module Data.HFunctor.HCompose where

import Data.HFunctor
import Data.Kind (Type)

newtype HCompose (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = HCompose { getHCompose :: h (k f) a }


instance (HFunctor h, HFunctor k, Functor m) => Functor (HCompose h k m) where
  fmap f (HCompose x) = HCompose (fmap f x)

instance (HFunctor h, HFunctor k) => HFunctor (HCompose h k) where
  hmap h (HCompose x) = HCompose (hmap (hmap h) x)

instance (HFunctor h, HFunctor k, Applicative (h (k f)), Applicative f) => (Applicative (HCompose h k f)) where
  pure x = HCompose (pure x)
  HCompose mf <*> HCompose mx = HCompose (mf <*> mx)
