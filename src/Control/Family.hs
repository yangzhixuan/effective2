{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Control.Family where
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Data.HFunctor
import Data.HFunctor.HCompose
import Data.HFunctor.HComposes

import Data.Kind ( Type )
import Control.Effect.Type

-- type family FamKind (a :: Effect)
-- type family FamSig (a :: Effect) :: FamKind (a :: Symbol) -> ((Type -> Type) -> (Type -> Type))

class ForwardT effs (t' :: (Type -> Type) -> (Type -> Type))  where
  fwdT :: forall t m . (Monad m, MonadTrans t)
      => Algebra effs (t m)
      -> Algebra effs (HCompose t' t m)

instance ForwardT '[] t' where
  fwdT :: forall t m . (Monad m, MonadTrans t)
      => Algebra '[] (t m)
      -> Algebra '[] (HCompose t' t m)
  fwdT alg = absurdEffs

class Forward effs (t :: (Type -> Type) -> (Type -> Type))  where
  fwd :: forall m . Monad m
      => Algebra effs m
      -> Algebra effs (t m)

instance {-# INCOHERENT #-} Forward '[] t where
  fwd :: forall m . Monad m
      => Algebra '[] (m)
      -> Algebra '[] (t m)
  fwd alg = absurdEffs

-- An experiment to remove stray IdentityT
-- {-# LANGUAGE AllowAmbiguousTypes #-}
-- type family LUnit t ts where
--   LUnit IdentityT ts = ts
--   LUnit t         ts = t ': ts
-- class ForwardTs effs (t :: Effect) where
--   fwdTs :: forall ts m . Monad m => Algebra effs (HComps ts m) -> Algebra effs (HComps (LUnit t ts) m)
--
-- instance ForwardTs effs IdentityT where
--   fwdTs alg = alg

instance {-# INCOHERENT #-} Forward effs IdentityT where
  fwd :: forall m . Monad m
    => Algebra effs m
    -> Algebra effs (IdentityT m)
  fwd alg x = (IdentityT . alg . hmap runIdentityT) x

instance {-# INCOHERENT #-}
  (Forward effs t1, Forward effs t2, MonadTrans t1, MonadTrans t2)
  => Forward effs (HCompose t1 t2) where
   fwd :: forall m . Monad m => Algebra effs m -> Algebra effs (HCompose t1 t2 m)
   fwd alg x = (HCompose . fwd (fwd alg) . hmap getHCompose) x

instance {-# INCOHERENT #-} Forward effs (HComps ('[])) where
   fwd :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps '[] m)
   fwd alg = HNil . alg . hmap unHNil

instance {-# INCOHERENT #-} (Forward effs t, Forward effs (HComps ts)
  , MonadTrans t, MonadTrans (HComps ts)) =>
  Forward effs (HComps (t ': ts)) where
   fwd :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps (t ': ts) m)
   fwd alg x = HCons . fwd (fwd alg) . hmap unHCons $ x

