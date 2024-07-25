{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Scoped where

import Control.Effect

import Data.Kind ( Type )
import Data.HFunctor

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

newtype Scp (lsig :: Type -> Type)
            (f :: Type -> Type)
            x
            = Scp (lsig (f x))

instance (Functor lsig, Functor f) => Functor (Scp lsig f) where
  {-# INLINE fmap #-}
  fmap f (Scp x) = Scp (fmap (fmap f) x)

instance Functor lsig => HFunctor (Scp lsig) where
  {-# INLINE hmap #-}
  hmap f (Scp x) = Scp (fmap f x)

instance Functor f => Forward (Scp f) IdentityT where
  {-# INLINE fwd #-}
  fwd alg (Scp op) = (IdentityT . alg . Scp . fmap runIdentityT) op

instance Functor f => Forward (Scp f) (ExceptT e) where
  {-# INLINE fwd #-}
  fwd alg (Scp op) = (ExceptT . alg . Scp . fmap runExceptT) op

instance Functor f => Forward (Scp f) MaybeT where
  {-# INLINE fwd #-}
  fwd alg (Scp op) = (MaybeT . alg . Scp . fmap runMaybeT) op

instance Functor f => Forward (Scp f) ListT where
  {-# INLINE fwd #-}
  fwd alg (Scp op) = (ListT . alg . Scp . fmap runListT) op

instance Functor f => Forward (Scp f) (StateT s) where
  {-# INLINE fwd #-}
  fwd alg (Scp op) = StateT (\s -> (alg (Scp (fmap (flip runStateT s) $ op))))

instance Functor f => Forward (Scp f) (WriterT s) where
  {-# INLINE fwd #-}
  fwd alg (Scp op) = WriterT (alg (Scp (fmap runWriterT op)))

instance Functor f => Forward (Scp f) (ReaderT w) where
  {-# INLINE fwd #-}
  fwd alg (Scp op) = ReaderT (\r -> alg (Scp (fmap (flip runReaderT r) op)))
