{-|
Module      : Control.Monad.Trans.Compose
Description : Higher-order functor composition
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ <= 904
{-# LANGUAGE QuantifiedConstraints #-}
#endif

module Control.Monad.Trans.Compose where

import Control.Monad.Trans.Class
import Data.Kind (Type)


-- | Right-to-left composition of higher-order functors. A higher-order version
-- of 'Data.Functor.Compose'.
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

#if __GLASGOW_HASKELL__ <= 904
instance (MonadTrans t1, MonadTrans t2, Monad m, Monad (t1(t2 m))) =>
#else
instance (MonadTrans t1, MonadTrans t2, Monad m) =>
#endif
  Monad (ComposeT t1 t2 m) where
    {-# INLINE (>>=) #-}
    (>>=) :: ComposeT t1 t2 m a -> (a -> ComposeT t1 t2 m b) -> ComposeT t1 t2 m b
    ComposeT mx >>= f = ComposeT (mx >>= getComposeT . f)

#if __GLASGOW_HASKELL__ <= 904
instance (MonadTrans t1, MonadTrans t2, forall m . Monad m => Monad (t2 m)) =>
#else
instance (MonadTrans t1, MonadTrans t2) =>
#endif
  MonadTrans (ComposeT t1 t2) where
    {-# INLINE lift #-}
    lift :: Monad m => m a -> ComposeT t1 t2 m a
    lift x = ComposeT (lift (lift x))