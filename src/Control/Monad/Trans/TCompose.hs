module Control.Monad.Trans.TCompose where

import Control.Monad.Trans.Class
import Data.Kind (Type)
import Control.Monad       (liftM, ap)


newtype TCompose (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = TCompose { getTCompose :: h (k f) a }

-- Monad transformers are closed under TCompose
instance (MonadTrans t1, MonadTrans t2) => MonadTrans (TCompose t1 t2) where
  lift x = TCompose (lift (lift x))

instance (MonadTrans t1, MonadTrans t2, Monad m) => Monad (TCompose t1 t2 m) where
  TCompose mx >>= f = TCompose (mx >>= getTCompose . f)

instance (MonadTrans t1, MonadTrans t2, Monad m) => Applicative (TCompose t1 t2 m) where
    pure x = TCompose (return x)
    (<*>) = ap

instance (MonadTrans t1, MonadTrans t2, Monad m) => Functor (TCompose t1 t2 m) where
    fmap = liftM
