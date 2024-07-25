{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Reader where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped

import qualified Control.Monad.Trans.Reader as R

type Ask r = Alg (Ask' r)
data Ask' r k where
  Ask :: (r -> k) -> Ask' r k
  deriving Functor

ask :: Member (Ask r) sig => Prog sig r
ask = call (Alg (Ask return))

asks :: Member (Ask r) sig => (r -> a) -> Prog sig a
asks f = fmap f ask

type Local r = Scp (Local' r)
data Local' r k where
  Local :: (r -> r) -> k -> Local' r k
  deriving Functor

local :: Member (Local r) sig => (r -> r) -> Prog sig a -> Prog sig a
local f p = call (Scp (Local f (fmap return p)))

reader :: r -> Handler [Ask r, Local r] '[] (R.ReaderT r) Identity
reader r = handler (fmap Identity . flip R.runReaderT r) readerAlg

readerAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Ask r, Local r] (R.ReaderT r m) x -> R.ReaderT r m x)
readerAlg oalg eff
  | Just (Alg (Ask p)) <- prj eff =
      do r <- R.ask
         return (p r)
  | Just (Scp (Local (f :: r -> r) (p))) <- prj eff =
      R.local f p
      -- do r <- R.ask
      --    lift (p (f r))
