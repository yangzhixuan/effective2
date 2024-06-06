{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Control.Family where
import Control.Monad.Trans.Class
import Control.Monad.Trans.TCompose

import Data.Kind ( Type )
import Control.Effect.Type

-- type family FamKind (a :: Effect)
-- type family FamSig (a :: Effect) :: FamKind (a :: Symbol) -> ((Type -> Type) -> (Type -> Type))

class Forward effs (t' :: (Type -> Type) -> (Type -> Type))  where
  fwd :: forall t m . (Monad m, MonadTrans t)
      => Algebra effs (t m)
      -> Algebra effs (TCompose t' t m)

instance Forward '[] t' where
  fwd :: forall t m . (Monad m, MonadTrans t)
      => Algebra '[] (t m)
      -> Algebra '[] (TCompose t' t m)
  fwd alg = absurdEffs
