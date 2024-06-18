{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Except where

import Control.Effect
import Control.Monad.Trans.Except
import Control.Family.Algebraic
import Control.Family.Scoped

data Throw' e k where
  Throw :: e -> Throw' e k
  deriving Functor

type Throw e = Alg (Throw' e)

throw :: forall e sig a . (Member (Throw e) sig) => e -> Prog sig a
throw e = (Call . inj @(Throw e)) (Alg (Throw e))

data Catch' e k where
  Catch :: k -> (e -> k) -> Catch' e k
  deriving Functor

type Catch e = Scp (Catch' e)

catch :: forall e sig a . Member (Catch e) sig => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catch p q = (Call . inj @(Catch e)) (Scp (Catch (fmap return p) (fmap return . q)))

exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw e, Catch e] (ExceptT e m) x -> ExceptT e m x)
exceptAlg _ eff
  | Just (Alg (Throw e)) <- prj eff
      = ExceptT (return (Left e))
  | Just (Scp (Catch p h)) <- prj eff
      = ExceptT $
                  do mx <- runExceptT p
                     case mx of
                       Left e  -> runExceptT (h e)
                       Right x -> return (Right x)

exceptT :: HandlerT '[Throw e, Catch e] '[] '[ExceptT e] '[Either e]
exceptT = handlerT' runExceptT exceptAlg

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

retryT :: HandlerT '[Throw e, Catch e] '[] '[ExceptT e] '[Either e]
retryT = handlerT' runExceptT retryAlg
