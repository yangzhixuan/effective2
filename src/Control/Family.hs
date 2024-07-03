{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Family where
import Control.Monad.Trans.Class
import Data.HFunctor
import Data.HFunctor.HCompose
import Data.HFunctor.HComposes

import Data.Kind ( Type )
import Control.Effect.Type

class Forward effs (t :: (Type -> Type) -> (Type -> Type))  where
  fwd :: forall m . Monad m
      => Algebra effs m
      -> Algebra effs (t m)

instance Forward '[] t where
  fwd :: forall m . Monad m
      => Algebra '[] (m)
      -> Algebra '[] (t m)
  fwd alg = absurdEffs

instance
  (Forward effs t1, Forward effs t2, MonadTrans t1, MonadTrans t2)
  => Forward effs (HCompose t1 t2) where
   fwd :: forall m . Monad m => Algebra effs m -> Algebra effs (HCompose t1 t2 m)
   fwd alg x = (HCompose . fwd (fwd alg) . hmap getHCompose) x

class Family fam t where
  fam :: forall m f . (Monad m, Functor f) => (forall x . (fam f) m x -> m x)
                                           -> (forall x . (fam f) (t m) x -> (t m) x)

instance (Family fam t, Functor f, Forward effs t) => Forward (fam f ': effs) t where
  fwd :: forall m . Monad m => Algebra (fam f ': effs) m -> Algebra (fam f ': effs) (t m)
  fwd alg (Eff op)   = fam @fam @t @m (alg . Eff) op
  fwd alg (Effs ops) = fwd (alg . Effs) ops

class (forall m . Monad m => Monad (HComps ts m)) => Forwards effs ts where
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps ts m)

instance Forwards effs '[] where
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps '[] m)
  fwds alg = HNil . alg . hmap unHNil

instance (forall m . Monad m => Monad (t (HComps ts m)), Forward effs t, Forwards effs ts)
  => Forwards effs (t ': ts) where
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps (t ': ts) m)
  fwds alg x = HCons . fwd (fwds alg) . hmap unHCons $ x
