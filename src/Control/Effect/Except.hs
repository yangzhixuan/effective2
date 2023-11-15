{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Except where

import Data.Functor.Composes ( comps )
import Data.HFunctor ( HFunctor(hmap) )
import Data.HFunctor.HComposes ( hdecomps, hcomps )

import Control.Effect
    ( Handler(Handler), Member(prj), Effs(..), Eff(Scp, Alg), handler )
import Control.Effect.Throw ( Throw(..) )
import Control.Effect.Catch ( Catch(..) )


import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class (MonadTrans, lift)

exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
exceptAlg oalg eff
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

except :: Handler [Throw, Catch] '[MaybeT] '[Maybe] '[]
except = handler runMaybeT exceptAlg exceptFwd


-- multiple semantics such as retry after handling is difficult in MTL
-- without resorting to entirely different newtype wrapping through
-- the whole program.
-- TODO: joinAlg
retryAlg :: Monad m
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
retryAlg oalg eff
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

-- retry :: Handler [Throw, Catch] '[MaybeT] '[Maybe] oeffs
-- retry = Handler
--   (const (fmap comps . runMaybeT . hdecomps))
--   (\oalg -> hcomps . retryAlg oalg . hmap hdecomps)
--   (\alg  -> hcomps . exceptFwd alg . hmap hdecomps)

retry :: Handler [Throw, Catch] '[MaybeT] '[Maybe] oeffs
retry = handler runMaybeT retryAlg exceptFwd

