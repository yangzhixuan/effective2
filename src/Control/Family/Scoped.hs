{-# LANGUAGE DataKinds #-}
module Control.Family.Scoped where

import Data.Kind ( Type )
import Data.HFunctor
import Control.Family
import Control.Effect.Type
import Control.Monad.Trans.Class

import Control.Monad.Trans.TCompose
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe

newtype Scp (lsig :: Type -> Type)
            (f :: Type -> Type)
            x
            = Scp (lsig (f x))

instance (Functor lsig, Functor f) => Functor (Scp lsig f) where
  fmap f (Scp x) = Scp (fmap (fmap f) x)

instance Functor lsig => HFunctor (Scp lsig) where
  hmap f (Scp x) = Scp (fmap f x)

instance (Functor f, Forward effs (ExceptT e)) => Forward (Scp f : effs) (ExceptT e) where
  fwd :: forall t m . (Monad m, MonadTrans t)
      => Algebra (Scp f : effs) (t m)
      -> Algebra (Scp f : effs) (TCompose (ExceptT e) t m)
  fwd alg (Eff (Scp op)) = TCompose (ExceptT (alg (Eff (Scp (fmap (runExceptT . getTCompose) op)))))
  fwd alg (Effs ops)     = fwd (alg . Effs) ops

instance (Functor f, Forward effs MaybeT) => Forward (Scp f : effs) MaybeT where
  fwd :: forall t m . (Monad m, MonadTrans t)
      => Algebra (Scp f : effs) (t m)
      -> Algebra (Scp f : effs) (TCompose MaybeT t m)
  fwd alg (Eff (Scp op)) = TCompose (MaybeT (alg (Eff (Scp (fmap (runMaybeT . getTCompose) op)))))
  fwd alg (Effs ops)     = fwd (alg . Effs) ops

