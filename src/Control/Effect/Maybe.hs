{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Maybe where

import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped

import Control.Family
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.TCompose

type Catch = Scp Catch'
data Catch' k where
  Catch :: k -> k -> Catch' k
  deriving Functor

catch :: Member Catch sig => Prog sig a -> Prog sig a -> Prog sig a
catch p q = (Call . inj) (Scp (Catch (fmap return p) (fmap return q)))

type Throw = Alg Throw'
data Throw' k where
  Throw :: Throw' k
  deriving Functor

throw :: Member Throw sig => Prog sig a
throw = (Call . inj) (Alg Throw)

exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
exceptAlg _ eff
  | Just (Alg Throw) <- prj eff
      = MaybeT (return Nothing)
  | Just (Scp (Catch p q)) <- prj eff
      = MaybeT $ do mx <- runMaybeT p
                    case mx of
                      Nothing -> runMaybeT q
                      Just x  -> return (Just x)

except :: Handler [Throw, Catch] '[] '[Maybe]
except = handler runMaybeT exceptAlg

exceptT
  :: forall effs oeffs fs t . (MonadTrans t, Forward effs MaybeT)
  => Handler' effs oeffs t fs
  -> Handler' (Throw : Catch : effs) oeffs (TCompose MaybeT t) (Maybe ': fs)
exceptT = handlerT @'[Throw, Catch] exceptAlg runMaybeT

-- multiple semantics such as retry after handling is difficult in MTL
-- without resorting to entirely different newtype wrapping through
-- the whole program.
--
-- The result of `retryAlg` on `catch p q` is to first try `p`.
-- If it fails, then `q` is executed as a recovering clause.
-- If the recovery fails then the computation is failed overall.
-- If the recovery succeeds, then `catch p q` is attempted again.
retryAlg :: Monad m
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
retryAlg _ eff
  | Just (Alg Throw) <- prj eff
      = MaybeT (return Nothing)
  | Just (Scp (Catch p q)) <- prj eff = MaybeT $ loop p q
      where
        loop p q =
          do mx <- runMaybeT p
             case mx of
               Nothing -> do my <- runMaybeT q
                             case my of
                               Nothing -> return Nothing
                               Just y  -> loop p q
               Just x  -> return (Just x)

retry :: Handler [Throw, Catch] '[] '[Maybe]
retry = handler runMaybeT retryAlg

retryT :: forall effs oeffs t fs
  .  (Forward effs MaybeT , MonadTrans t)
  => Handler' effs oeffs t fs
  -> Handler' (Throw : Catch : effs)
              oeffs (TCompose MaybeT t)
              (Maybe : fs)
retryT = handlerT @'[Throw, Catch] retryAlg runMaybeT

