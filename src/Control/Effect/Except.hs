{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Except where

import Control.Effect
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift)

data Throw e k where
  Throw :: e -> Throw e k
  deriving Functor

throw :: forall e sig a . (Member (Throw e) sig) => e -> Prog sig a
throw e = (Call . inj @(Throw e)) (Alg (Throw e))

data Catch e k where
  Catch :: k -> (e -> k) -> Catch e k
  deriving Functor

exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw e, Catch e] (ExceptT e m) x -> ExceptT e m x)
exceptAlg _ eff
  | Just (Alg (Throw e)) <- prj eff
      = ExceptT (return (Left e))
  | Just (Scp (Catch p h)) <- prj eff
      = ExceptT $ do mx <- runExceptT p
                     case mx of
                       Left e  -> runExceptT (h e)
                       Right x -> return (Right x)

exceptFwd
  :: Monad m
  => (forall x. Effs sigs m x -> m x)
  -> (forall x. Effs sigs (ExceptT e m) x -> ExceptT e m x)
exceptFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
exceptFwd alg (Eff (Scp x)) = ExceptT (alg (Eff (Scp (fmap runExceptT x))))
exceptFwd alg (Effs effs)   = exceptFwd (alg . Effs) effs

except :: Handler [Throw e, Catch e] '[] '[Either e]
except = handler runExceptT exceptAlg exceptFwd

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
  -> (forall x. Effs [Throw e, Catch e] (ExceptT e m) x -> ExceptT e m x)
retryAlg _ eff
  | Just (Alg (Throw e)) <- prj eff
      = ExceptT (return (Left e))
  | Just (Scp (Catch p h)) <- prj eff = ExceptT $ loop p h
      where
        loop p h =
          do mx <- runExceptT p
             case mx of
               Left e -> do my <- runExceptT (h e)
                            case my of
                              Left e' -> return (Left e')
                              Right y  -> loop p h
               Right x  -> return (Right x)

retry :: Handler [Throw e, Catch e] '[] '[Either e]
retry = handler runExceptT retryAlg exceptFwd

