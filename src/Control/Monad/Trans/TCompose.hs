module Control.Monad.Trans.TCompose where

import Control.Monad

import Control.Monad.Trans.Class
import Data.Kind (Type)

-- Monad transformers are closed under TCompose, but there is not enough
-- structure to establish `HFunctor`, since
-- `hmap :: (Functor f, Functor g) => ...` is between two *functors* `f` and `g`.
-- Consequently, `MonadTrans t1 f` cannot be formed.

-- It is tempting to weaken all the constraints in the following from `Monad`
-- to `Applicative` or `Functor`, but it does not help: `MonadTrans` requires
-- that the parameter it relies on is `Monad` anyway.
newtype TCompose (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = TCompose { getTCompose :: h (k f) a }

instance (MonadTrans t1, MonadTrans t2, Monad m) =>
  Functor (TCompose t1 t2 m) where
    fmap :: (a -> b) -> TCompose t1 t2 m a -> TCompose t1 t2 m b
    fmap = liftM

instance (MonadTrans t1, MonadTrans t2, Monad m) =>
  Applicative (TCompose t1 t2 m) where
    pure :: (MonadTrans t1, MonadTrans t2, Monad m) =>
      a -> TCompose t1 t2 m a
    pure x = TCompose (return x)

    (<*>) :: (MonadTrans t1, MonadTrans t2, Applicative m) =>
      TCompose t1 t2 m (a -> b) -> TCompose t1 t2 m a -> TCompose t1 t2 m b
    TCompose mf <*> TCompose mx = TCompose (mf <*> mx)

instance (MonadTrans t1, MonadTrans t2, Monad m) =>
  Monad (TCompose t1 t2 m) where
    (>>=) :: (MonadTrans t1, MonadTrans t2, Monad m) =>
      TCompose t1 t2 m a -> (a -> TCompose t1 t2 m b) -> TCompose t1 t2 m b
    TCompose mx >>= f = TCompose (mx >>= getTCompose . f)

instance (MonadTrans t1, MonadTrans t2) =>
  MonadTrans (TCompose t1 t2) where
    lift :: Monad m => m a -> TCompose t1 t2 m a
    lift x = TCompose (lift (lift x))