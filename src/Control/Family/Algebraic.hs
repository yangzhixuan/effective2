{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Family.Algebraic where

import Data.Kind ( Type )
import Data.HFunctor
import Control.Family
import Control.Monad.Trans.Class

newtype Alg (lsig :: Type -> Type)
            (f :: Type -> Type)
            x
            = Alg (lsig x)

instance Functor lsig => Functor (Alg lsig f) where
  fmap f (Alg x) = Alg (fmap f x)

instance Functor lsig => HFunctor (Alg lsig) where
  hmap f (Alg x) = Alg x

instance MonadTrans t => Family Alg t where
  fam alg (Alg op) = lift (alg (Alg op))
