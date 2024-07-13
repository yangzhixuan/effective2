{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Family where
import Data.HFunctor
import Data.HFunctor.HComposes

import Data.Kind ( Type )
import Control.Effect.Type

class Family fam t where
  fam :: forall m f . (Monad m, Functor f)
      => (forall x . (fam f) m x -> m x)
      -> (forall x . (fam f) (t m) x -> (t m) x)

class Forward (eff :: Effect) (t :: Effect) where
  fwd :: forall m . (Monad m)
       => (forall x . eff m x  -> m x)
       -> (forall x . eff (t m) x -> t m x)

-- The default implementation comes from a family if it is available.
-- This can be overlapped with a custom forwarder for a specific effect
-- if desired.
instance {-# OVERLAPPABLE #-} (Family fam t, Functor f) => Forward (fam f) t where
  fwd = fam

-- This class builds a forwarder for an `Effs` by recursion over `effs`,
-- by ensuring that each effect can be forwarded through a given `t`.
class ForwardEffs effs (t :: (Type -> Type) -> (Type -> Type))  where
  fwdEffs :: forall m . Monad m
    => Algebra effs m
    -> Algebra effs (t m)

instance ForwardEffs '[] t where
  fwdEffs :: forall m . Monad m
    => Algebra '[] (m)
    -> Algebra '[] (t m)
  fwdEffs alg = absurdEffs

instance (Forward eff t, ForwardEffs effs t) => ForwardEffs (eff ': effs) t where
  fwdEffs :: forall m . Monad m => Algebra (eff ': effs) m -> Algebra (eff ': effs) (t m)
  fwdEffs alg (Eff op)   = fwd (alg . Eff) op
  fwdEffs alg (Effs ops) = fwdEffs (alg . Effs) ops

-- The `Forwards` class forwards effects through a transformer stack, assuming
-- that for each member of the stack, all operations in `effs` can be forwarded.
class (forall m . Monad m => Monad (HComps ts m)) => Forwards effs ts where
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps ts m)

instance Forwards effs '[] where
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps '[] m)
  fwds alg = HNil . alg . hmap unHNil

instance (forall m . Monad m => Monad (t (HComps ts m)), ForwardEffs effs t, Forwards effs ts)
  => Forwards effs (t ': ts) where
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps (t ': ts) m)
  fwds alg x = HCons . fwdEffs (fwds alg) . hmap unHCons $ x

