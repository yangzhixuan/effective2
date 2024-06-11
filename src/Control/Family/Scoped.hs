{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Family.Scoped where

import Data.Kind ( Type )
import Data.HFunctor
import Control.Family
import Control.Effect.Type
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity

import Data.HFunctor.HCompose
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Writer

newtype Scp (lsig :: Type -> Type)
            (f :: Type -> Type)
            x
            = Scp (lsig (f x))

instance (Functor lsig, Functor f) => Functor (Scp lsig f) where
  fmap f (Scp x) = Scp (fmap (fmap f) x)

instance Functor lsig => HFunctor (Scp lsig) where
  hmap f (Scp x) = Scp (fmap f x)

instance (Functor f, ForwardT effs IdentityT) =>
  ForwardT (Scp f : effs) IdentityT where
  fwdT :: forall t m . (Monad m, MonadTrans t)
      => Algebra (Scp f : effs) (t m)
      -> Algebra (Scp f : effs) (HCompose IdentityT t m)
  fwdT alg (Eff (Scp op)) = HCompose (IdentityT (alg (Eff (Scp (fmap (runIdentityT . getHCompose) op)))))
  fwdT alg (Effs ops)     = fwdT (alg . Effs) ops

instance (Functor f, ForwardT effs (ExceptT e)) =>
  ForwardT (Scp f : effs) (ExceptT e) where
    fwdT :: forall t m . (Monad m, MonadTrans t)
        => Algebra (Scp f : effs) (t m)
        -> Algebra (Scp f : effs) (HCompose (ExceptT e) t m)
    fwdT alg (Eff (Scp op)) = HCompose (ExceptT (alg (Eff (Scp (fmap (runExceptT . getHCompose) op)))))
    fwdT alg (Effs ops)     = fwdT (alg . Effs) ops

instance (Functor f, ForwardT effs MaybeT) =>
  ForwardT (Scp f : effs) MaybeT where
    fwdT :: forall t m . (Monad m, MonadTrans t)
        => Algebra (Scp f : effs) (t m)
        -> Algebra (Scp f : effs) (HCompose MaybeT t m)
    fwdT alg (Eff (Scp op)) = HCompose (MaybeT (alg (Eff (Scp (fmap (runMaybeT . getHCompose) op)))))
    fwdT alg (Effs ops)     = fwdT (alg . Effs) ops

instance (Functor f, Forward effs IdentityT) =>
  Forward (Scp f : effs) IdentityT where
    fwd :: forall m . (Monad m)
        => Algebra (Scp f : effs) (m)
        -> Algebra (Scp f : effs) (IdentityT m)
    fwd alg (Eff (Scp op)) = (IdentityT . alg . Eff . Scp . fmap runIdentityT) op
    fwd alg (Effs ops)     = fwd (alg . Effs) ops

instance (Functor f, Forward effs (ExceptT e)) =>
  Forward (Scp f : effs) (ExceptT e) where
    fwd :: forall m . (Monad m)
        => Algebra (Scp f : effs) (m)
        -> Algebra (Scp f : effs) (ExceptT e m)
    fwd alg (Eff (Scp op)) = (ExceptT . alg . Eff . Scp . fmap runExceptT) op
    fwd alg (Effs ops)     = fwd (alg . Effs) ops

instance (Functor f, Forward effs MaybeT) =>
  Forward (Scp f : effs) MaybeT where
    fwd :: forall m . (Monad m)
        => Algebra (Scp f : effs) (m)
        -> Algebra (Scp f : effs) (MaybeT m)
    fwd alg (Eff (Scp op)) = (MaybeT . alg . Eff . Scp . fmap runMaybeT) op
    fwd alg (Effs ops)     = fwd (alg . Effs) ops

instance (Functor f, Forward effs ListT) =>
  Forward (Scp f : effs) ListT where
    fwd :: forall m . (Monad m)
        => Algebra (Scp f : effs) (m)
        -> Algebra (Scp f : effs) (ListT m)
    fwd alg (Eff (Scp op)) = (ListT . alg . Eff . Scp . fmap runListT) op
    fwd alg (Effs ops)     = fwd (alg . Effs) ops

instance (Functor f, Forward effs (StateT s)) =>
  Forward (Scp f : effs) (StateT s) where
    fwd :: forall m . (Monad m)
        => Algebra (Scp f : effs) (m)
        -> Algebra (Scp f : effs) (StateT s m)
    fwd alg (Eff (Scp op)) = StateT (\s -> (alg (Eff (Scp (fmap (flip runStateT s) $ op)))))
    fwd alg (Effs ops)     = fwd (alg . Effs) ops

instance (Functor f, Forward effs (WriterT w)) =>
  Forward (Scp f : effs) (WriterT w) where
    fwd :: forall m . (Monad m)
        => Algebra (Scp f : effs) (m)
        -> Algebra (Scp f : effs) (WriterT w m)
    fwd alg (Eff (Scp op)) = WriterT (alg (Eff (Scp (fmap runWriterT op))))
    fwd alg (Effs ops)     = fwd (alg . Effs) ops



