{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Except where

import Control.Effect
import Control.Family
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Control.Monad.Trans.TCompose
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

exceptT
  :: forall effs oeffs fs t e . (MonadTrans t, Forward effs (ExceptT e))
  => Handler' effs oeffs t fs
  -> Handler' (Throw e : Catch e : effs) oeffs (TCompose (ExceptT e) t) (Either e ': fs)
exceptT = handlerT @'[Throw e, Catch e] exceptAlg runExceptT

--except
--  :: forall effs oeffs fs t e . (MonadTrans t, Forward effs (ExceptT e))
--  => Handler' effs oeffs t fs
--  -> Handler' (Throw e : Catch e : effs) oeffs (TCompose (ExceptT e) t) (Either e ': fs)
--except (Handler' run malg _mfwd) = Handler' run' malg' undefined where
--  run'  :: forall m . Monad m
--       => (forall x . Effs oeffs m x -> m x)
--       -> (forall x . TCompose (ExceptT e) t m x -> m (RComps (Either e ': fs) x))
--  run' oalg x = fmap RCCons (run oalg ((runExceptT . getTCompose) x))
--
--  malg' :: forall m . Monad m
--       => (forall x . Effs oeffs m x -> m x)
--       -> (forall x . Effs (Throw e : Catch e : effs) (TCompose (ExceptT e) t m) x
--             -> TCompose (ExceptT e) t m x)
--  malg' oalg (Eff (Alg (Throw e)))        = TCompose (ExceptT (return (Left e)))
--  malg' oalg (Effs (Eff (Scp (Catch p h))))
--      = TCompose $ ExceptT $
--                  do mx <- runExceptT . getTCompose $ p
--                     case mx of
--                       Left e  -> runExceptT (getTCompose (h e))
--                       Right x -> return (Right x)
--  malg' oalg (Effs (Effs op))             = fwd (malg oalg) op


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


retryT :: forall effs oeffs t fs e
  .  (Forward effs (ExceptT e), MonadTrans t)
  => Handler' effs oeffs t fs
  -> Handler' (Throw e : Catch e : effs)
              oeffs (TCompose (ExceptT e) t)
              (Either e : fs)
retryT = handlerT @'[Throw e, Catch e] retryAlg runExceptT
