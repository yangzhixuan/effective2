{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Control.Family where
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Data.HFunctor
import Data.HFunctor.HCompose

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
