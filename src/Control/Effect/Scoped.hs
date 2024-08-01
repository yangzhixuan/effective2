{-|
Module      : Control.Effect.Scoped
Description : The scoped effect family
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Scoped where

import Control.Effect

import Data.Kind ( Type )
import Data.HFunctor

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

-- | The family of scoped operations. Forwarding scoped operations through a
-- transformer must be given explicitly using the `Forward` class.
-- newtype Scp (lsig :: Type -> Type)
--             (f :: Type -> Type)
--             x
--             = Scp (lsig (f x))

data Scp (lsig :: Type -> Type)
          (f :: Type -> Type)
          x
          = forall y z . Scp (lsig y) (y -> f z) (z -> x)

instance (Functor lsig, Functor f) => Functor (Scp lsig f) where
  {-# INLINE fmap #-}
  fmap f (Scp x h k) = Scp x h (f . k)

instance Functor lsig => HFunctor (Scp lsig) where
  {-# INLINE hmap #-}
  hmap f (Scp x h k) = Scp x (f . h) k

instance Functor f => Forward (Scp f) IdentityT where
  {-# INLINE fwd #-}
  fwd alg (Scp op h k) = IdentityT (alg (Scp op (runIdentityT . h) k))

instance Functor f => Forward (Scp f) (ExceptT e) where
  {-# INLINE fwd #-}
  fwd alg (Scp op h k) = ExceptT (alg (Scp op (runExceptT . h) (fmap k)))

instance Functor f => Forward (Scp f) MaybeT where
  {-# INLINE fwd #-}
  fwd alg (Scp op h k) = MaybeT (alg (Scp op  (runMaybeT . h) (fmap k)))

instance Functor f => Forward (Scp f) (StateT s) where
  {-# INLINE fwd #-}
  fwd alg (Scp op h k) = StateT (\s -> (alg (Scp op (flip runStateT s . h) (\(z, s) -> (k z, s)))))

instance Functor f => Forward (Scp f) (WriterT s) where
  {-# INLINE fwd #-}
  fwd alg (Scp op h k) = WriterT (alg (Scp op (runWriterT . h) (\(z, s) -> (k z, s))))

instance Functor f => Forward (Scp f) (ReaderT w) where
  {-# INLINE fwd #-}
  fwd alg (Scp op h k) = ReaderT (\r -> alg (Scp op (flip runReaderT r . h) k))
