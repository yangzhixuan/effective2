module Data.HFunctor.HCompose where

import Data.HFunctor
import Control.Monad.Trans.Class
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

instance (HFunctor t1, HFunctor t2, Monad m, Monad (t1 (t2 m))) => (Monad (HCompose t1 t2 m)) where
  HCompose mx >>= f = HCompose (mx >>= getHCompose . f)

instance (MonadTrans t1, MonadTrans t2, HFunctor t1, HFunctor t2) => MonadTrans (HCompose t1 t2) where
  lift x = HCompose (lift (lift x))

