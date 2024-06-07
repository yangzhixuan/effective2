module Data.HFunctor.HCompose where

import Data.HFunctor
import Control.Monad.Trans.Class
import Data.Kind (Type)

newtype HCompose (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = HCompose { getHCompose :: h (k f) a }

instance (HFunctor h, HFunctor k, Functor m) =>
  Functor (HCompose h k m) where
    fmap :: (HFunctor h, HFunctor k, Functor m) =>
      (a -> b) -> HCompose h k m a -> HCompose h k m b
    fmap f (HCompose x) = HCompose (fmap f x)

instance (HFunctor h, HFunctor k, Applicative (h (k f)), Applicative f) =>
  Applicative (HCompose h k f) where
    pure :: (HFunctor h, HFunctor k, Applicative (h (k f)), Applicative f) =>
      a -> HCompose h k f a
    pure x = HCompose (pure x)

    (<*>) :: (HFunctor h, HFunctor k, Applicative (h (k f)), Applicative f) =>
      HCompose h k f (a -> b) -> HCompose h k f a -> HCompose h k f b
    HCompose mf <*> HCompose mx = HCompose (mf <*> mx)

instance (MonadTrans t1, MonadTrans t2, HFunctor t1, HFunctor t2, Monad m) => Monad (HCompose t1 t2 m) where
  (>>=) :: (MonadTrans t1, MonadTrans t2, HFunctor t1, HFunctor t2, Monad m) =>
    HCompose t1 t2 m a -> (a -> HCompose t1 t2 m b) -> HCompose t1 t2 m b
  HCompose mx >>= f = HCompose (mx >>= getHCompose . f)

instance (MonadTrans t1, MonadTrans t2, HFunctor t1, HFunctor t2) =>
  MonadTrans (HCompose t1 t2) where
  lift :: (MonadTrans t1, MonadTrans t2, HFunctor t1, HFunctor t2, Monad m) =>
    m a -> HCompose t1 t2 m a
  lift x = HCompose (lift (lift x))

instance (HFunctor h, HFunctor k) =>
  HFunctor (HCompose h k) where
    hmap :: (HFunctor h, HFunctor k, Functor f, Functor g) =>
      (forall x. f x -> g x) -> HCompose h k f a -> HCompose h k g a
    hmap h (HCompose x) = HCompose (hmap (hmap h) x)
