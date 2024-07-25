{-# LANGUAGE TypeFamilies #-}

module Control.Monad.Trans.Compose where

import Data.HFunctor
import Control.Monad.Trans.Class
import Data.Kind (Type)

newtype ComposeT (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = ComposeT { getComposeT :: h (k f) a }

instance Functor (h (k m)) => Functor (ComposeT h k m) where
    {-# INLINE fmap #-}
    fmap :: (a -> b) -> ComposeT h k m a -> ComposeT h k m b
    fmap f (ComposeT x) = ComposeT (fmap f x)

instance (Applicative (h (k f)), Applicative f) =>
  Applicative (ComposeT h k f) where
    {-# INLINE pure #-}
    pure :: a -> ComposeT h k f a
    pure x = ComposeT (pure x)

    {-# INLINE (<*>) #-}
    (<*>) :: ComposeT h k f (a -> b) -> ComposeT h k f a -> ComposeT h k f b
    ComposeT mf <*> ComposeT mx = ComposeT (mf <*> mx)

instance (MonadTrans t1, MonadTrans t2, Monad m) =>
  Monad (ComposeT t1 t2 m) where
    {-# INLINE (>>=) #-}
    (>>=) :: ComposeT t1 t2 m a -> (a -> ComposeT t1 t2 m b) -> ComposeT t1 t2 m b
    ComposeT mx >>= f = ComposeT (mx >>= getComposeT . f)

instance (MonadTrans t1, MonadTrans t2) =>
  MonadTrans (ComposeT t1 t2) where
    {-# INLINE lift #-}
    lift :: Monad m => m a -> ComposeT t1 t2 m a
    lift x = ComposeT (lift (lift x))

instance (HFunctor h, HFunctor k) =>
  HFunctor (ComposeT h k) where
    {-# INLINE hmap #-}
    hmap :: (HFunctor h, HFunctor k, Functor f, Functor g) =>
      (forall x. f x -> g x) -> ComposeT h k f a -> ComposeT h k g a
    hmap h (ComposeT x) = ComposeT (hmap (hmap h) x)
