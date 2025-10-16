{-|
Module      : Control.Effect.Reader
Description : Effects for the reader monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Effect.Reader (
  -- * Syntax
  -- ** Operations
  ask,
  asks,
  local,

  -- ** Signatures
  pattern Ask,
  Ask, Ask_(..),
  Local, Local_(..),

  -- * Semantics
  -- ** Handlers
  reader,
  reader',
  readerAsk,
  asker,

  -- ** Algebras
  readerAT,
  readerAskAT,

  -- ** Underlying monad transformers
  R.ReaderT(..),
) where

import Control.Effect
import Control.Effect.Internal.AlgTrans
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Data.Functor.Unary
import Control.Effect.Internal.TH

import qualified Control.Monad.Trans.Reader as R

-- | Underlying signature for asking for the environment.
data Ask_ r k where
  Ask_ :: (r -> k) -> Ask_ r k
  deriving Functor

-- The following can be generated with:
$(makeAlg ''Ask_)

{-
-- | Signature for asking for the environment.
type Ask r = Alg (Ask_ r)

pattern Ask :: Member (Ask r) sig => (r -> k) -> Effs sig m k
pattern Ask k <- (prj -> Just (Alg (Ask_ k)))
  where Ask k = inj (Alg (Ask_ k))

-- | Fetch the value of the environment.
{-# INLINE ask #-}
ask :: Member (Ask r) sig => Prog sig r
ask = call (Alg (Ask_ id))
-}


-- | Retrieve a function of the current environment.
{-# INLINE asks #-}
asks :: Member (Ask r) sig
  => (r -> a) -- ^ The selector function to apply to the environment
  -> Prog sig a
asks f = fmap f ask

-- | Signature for 'local' operation
type Local r = Scp (Local_ r)

-- | Underlying signature for 'local' operation
data Local_ r k where
  Local :: (r -> r) -> k -> Local_ r k
  deriving Functor

instance Unary (Local_ r) where
  get (Local _ x) = x

-- | Execute a computation in a transformed environment
{-# INLINE local #-}
local :: Member (Local r) sig
  => (r -> r)    -- ^ Function to transform the environment
  -> Prog sig a  -- ^ Computation to run in the transformed environment
  -> Prog sig a
local f p = call (Scp (Local f p))

-- | The `reader` handler supplies a static environment @r@ to the program
-- that can be accessed with `ask`, and locally transformed with `local`.
{-# INLINE reader #-}
reader :: r -> Handler [Ask r, Local r] '[] '[R.ReaderT r] a a
reader r = handler' (flip R.runReaderT r) (\_ -> readerAlg)
--       = (\_ -> readerAlg) #: runner (flip R.runReaderT r)

-- | The `reader'` handler supplies an environment @r@ computed using the
-- output effects to the program that can be accessed with `ask`, and
-- locally transformed with `local`.
{-# INLINE reader' #-}
reader' :: forall oeffs r a . (forall m . Monad m => Algebra oeffs m -> m r)
        -> Handler [Ask r, Local r] oeffs '[R.ReaderT r] a a
reader' mr = handler run (\_ -> readerAlg) where
  run :: forall m . Monad m => Algebra oeffs m
      -> (R.ReaderT r m a -> m a)
  run oalg rmx = do r <- mr oalg
                    x <- R.runReaderT rmx r
                    return x

-- | The algebra for the 'reader' handler.
{-# INLINE readerAlg #-}
readerAlg
  :: Monad m => Algebra [Ask r, Local r] (R.ReaderT r m)
readerAlg eff
  | Just (Alg (Ask_ p)) <- prj eff =
      do r <- R.ask
         return (p r)
  | Just (Scp (Local (f :: r -> r) p)) <- prj eff =
      R.local f p

readerAT :: AlgTrans '[Ask r, Local r] '[] '[R.ReaderT r] Monad
readerAT = AlgTrans (\_ -> readerAlg)

readerAskAT :: AlgTrans '[Ask r] '[] '[R.ReaderT r] Monad
readerAskAT = weakenIEffs readerAT

readerAsk :: r -> Handler '[Ask r] '[] '[R.ReaderT r] a a
readerAsk r = handler' (flip R.runReaderT r) (getAT readerAskAT)

asker :: r -> Handler '[Ask r] '[] '[] a a
asker r = interpret (\(Ask k) -> return (k r))