{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Family.Algebraic where

import Data.Kind ( Type )
import Data.HFunctor
import Control.Family
import Control.Effect.Type
import Control.Monad.Trans.Class

import Data.HFunctor.HCompose

newtype Alg (lsig :: Type -> Type)
            (f :: Type -> Type)
            x
            = Alg (lsig x)

instance Functor lsig => Functor (Alg lsig f) where
  fmap f (Alg x) = Alg (fmap f x)

instance Functor lsig => HFunctor (Alg lsig) where
  hmap f (Alg x) = Alg x

instance (MonadTrans t', ForwardT effs t') => ForwardT (Alg f ': effs) t' where
  fwdT :: forall t m . (Monad m, MonadTrans t)
      => Algebra (Alg f : effs) (t m)
      -> Algebra (Alg f : effs) (HCompose t' t m)
  fwdT alg (Eff (Alg op)) = HCompose (lift (alg (Eff (Alg op))))
  fwdT alg (Effs ops)     = fwdT (alg . Effs) ops

instance (MonadTrans t', Forward effs t') => Forward (Alg f ': effs) t' where
  fwd :: forall m . (Monad m)
      => Algebra (Alg f : effs) (m)
      -> Algebra (Alg f : effs) (t' m)
  fwd alg (Eff (Alg op)) = (lift (alg (Eff (Alg op))))
  fwd alg (Effs ops)     = fwd (alg . Effs) ops
