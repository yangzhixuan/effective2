{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Algebraic where

import Control.Effect

import Data.Kind ( Type )
import Data.HFunctor
import Control.Monad.Trans.Class

newtype Alg (lsig :: Type -> Type)
            (f :: Type -> Type)
            x
            = Alg (lsig x)

instance Functor lsig => Functor (Alg lsig f) where
  fmap f (Alg x) = Alg (fmap f x)

instance Functor lsig => HFunctor (Alg lsig) where
  hmap f (Alg x) = Alg x

instance (Functor f, MonadTrans t) => Forward (Alg f) t where
  fwd alg (Alg op) = lift (alg (Alg op))
