{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Maybe where

import Control.Effect

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class (lift)

-- TODO: Consider renaming catch/Throw/Catch to lobby/Exit/Enter

data Catch k where
  Catch :: k -> k -> Catch k
  deriving Functor

catch :: Member Catch sig => Prog sig a -> Prog sig a -> Prog sig a
catch p q = injCall (Scp (Catch (fmap return p) (fmap return q)))

data Throw k where
  Throw :: Throw k
  deriving Functor

throw :: Member Throw sig => Prog sig a
throw = injCall (Alg Throw)

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

exceptFwd
  :: Monad m
  => (forall x. Effs sigs m x -> m x)
  -> (forall x. Effs sigs (MaybeT m) x -> MaybeT m x)
exceptFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
exceptFwd alg (Eff (Scp x)) = MaybeT (alg (Eff (Scp (fmap runMaybeT x))))
exceptFwd alg (Effs effs)   = exceptFwd (alg . Effs) effs

except :: Handler [Throw, Catch] '[] '[Maybe]
except = handler runMaybeT exceptAlg exceptFwd

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
retry = handler runMaybeT retryAlg exceptFwd

