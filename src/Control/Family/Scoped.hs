{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Family.Scoped where

import Data.Kind ( Type )
import Data.HFunctor
import Control.Family
import Control.Monad.Trans.Identity

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
  fmap f (Scp x) = Scp (fmap (fmap f) x)

instance Functor lsig => HFunctor (Scp lsig) where
  hmap f (Scp x) = Scp (fmap f x)

instance Family Scp IdentityT where
  fam alg (Scp op) = (IdentityT . alg . Scp . fmap runIdentityT) op

instance Family Scp (ExceptT e) where
  fam alg (Scp op) = (ExceptT . alg . Scp . fmap runExceptT) op

instance Functor f => Forward (Scp f) (ExceptT e) where
  fwd alg (Scp op) = (ExceptT . alg . Scp . fmap runExceptT) op

instance Family Scp MaybeT where
  fam alg (Scp op) = (MaybeT . alg . Scp . fmap runMaybeT) op

instance Family Scp ListT where
  fam alg (Scp op) = (ListT . alg . Scp . fmap runListT) op

instance Family Scp (StateT s) where
  fam alg (Scp op) = StateT (\s -> (alg (Scp (fmap (flip runStateT s) $ op))))

instance Family Scp (WriterT s) where
  fam alg (Scp op) = WriterT (alg (Scp (fmap runWriterT op)))

instance Family Scp (ReaderT w) where
  fam alg (Scp op) = ReaderT (\r -> alg (Scp (fmap (flip runReaderT r) op)))
