{-|
Module      : Control.Effect.IO
Description : Effects for input/output
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}

module Control.Effect.IO (
  -- * Syntax
  -- ** Operations
  io,

  -- * Semantics
  -- * Evaluation
  evalIO,
  handleIO,
  handleIO',

  -- * Algebras
  ioAlg,
  nativeAlg,
)
  where

import Control.Effect
import Control.Effect.Internal.Handler
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Family.Distributive
import Control.Effect.Concurrency.Type (Par, Par_(..), JPar, JPar_(..))
import Data.List.Kind
import Data.HFunctor

-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra '[Alg IO] IO
ioAlg = nativeAlg

-- | Treating an IO computation as an operation of signature `Alg IO`.
io :: Members '[Alg IO] sig => IO a -> Prog sig a
io op = call (Alg op)

-- | @`evalIO` p@ evaluates all IO operations in @p@ in the `IO` monad
-- using their standard semantics.
evalIO :: Prog '[Alg IO] a -> IO a
evalIO = eval ioAlg

-- | @`handleIO` h p@ evaluates @p@ using the handler @h@. Any residual
-- effects are then interpreted in `IO` using their standard semantics, but
-- IO effects are not forwarded along the handler.
handleIO
  :: forall effs ts fs a
  . ( Monad (Apply ts IO)
    , HFunctor (Effs effs) )
  => Handler effs '[Alg IO] ts fs
  -> Prog effs a -> IO (Apply fs a)
handleIO = handleM' @effs ioAlg

type HandleIO# effs oeffs xeffs =
  ( Injects (xeffs :\\ effs) xeffs
  , Append effs (xeffs :\\ effs)
  , HFunctor (Effs (effs `Union` xeffs)))

-- | @`handleIO` h p@ evaluates @p@ using the handler @h@. The handler may
-- output some effects that are a subset of the IO effects and additionally
-- the program may also use a subset @xeffs@ of the IO effects (which must
-- be forwardable through the monad transformer @ts@).
-- The type argument @xeffs@ usually can't be inferred and needs given
-- explicitly.
-- This function is useful when you want to use some non-algebraic operations
-- that come with the IO-monad. Otherwise `handleIO` should be used.
handleIO'
  :: forall xeffs ioeff effs oeffs ts fs a
  . ( Injects oeffs ioeff
    , ForwardsM xeffs ts
    , Monad (Apply ts IO)
    , Injects xeffs ioeff
    , HandleIO# effs oeffs xeffs )
  => Proxy xeffs 
  -> Algebra ioeff IO
  -> Handler effs oeffs ts fs
  -> Prog (effs `Union` xeffs) a -> IO (Apply fs a)
handleIO' p ioAlg h = handleMFwds p ioAlg h