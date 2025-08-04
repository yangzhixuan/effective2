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

  -- ** Signatures
  IOEffects,

  -- * Semantics
  -- * Evaluation
  evalIO,
  handleIO,
  handleIO',

  -- * Algebras
  ioAlg,
  nativeAlg,
  parAlg,
  jparAlg,
)
  where

import Control.Effect
import Control.Effect.Internal.Handler
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Family.Distributive
import Control.Effect.Concurrency.Type (Par, Par_(..), JPar, JPar_(..))

import qualified Control.Concurrent
import qualified Control.Concurrent.MVar as MVar
import Data.List.Kind
import Data.HFunctor


-- | All effectful operations that the IO monad supports natively
type IOEffects = '[Alg IO, Par, JPar]


-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra IOEffects IO
ioAlg = nativeAlg # parAlg # jparAlg

-- | Treating an IO computation as an operation of signature `Alg IO`.
io :: Members '[Alg IO] sig => IO a -> Prog sig a
io op = call (Alg op)

-- | Interprets t`Control.Effect.Concurrency.Par` using the native concurrency API.
-- from `Control.Concurrent`.
parAlg :: Algebra '[Par] IO
parAlg eff
  | Just (Scp (Par l r)) <- prj eff =
      do Control.Concurrent.forkIO (fmap (const ()) r)
         l

-- | Interprets t`Control.Effect.Concurrency.JPar` using the native concurrency API.
-- from "Control.Concurrent". The result from the child thread is passed back to the
-- main thread using @MVar@.
jparAlg :: Algebra '[JPar] IO
jparAlg eff
  | Just (Distr (JPar l r) c) <- prj eff =
      do m <- MVar.newEmptyMVar
         Control.Concurrent.forkIO $
           do y <- r; MVar.putMVar m y
         x <- l
         y' <- MVar.takeMVar m
         return (c (JPar x y'))


-- | @`evalIO` p@ evaluates all IO operations in @p@ in the `IO` monad
-- using their standard semantics.
evalIO :: Prog IOEffects a -> IO a
evalIO = eval ioAlg

type HandleIO# effs oeffs xeffs =
  ( Injects (xeffs :\\ effs) xeffs
  , Append effs (xeffs :\\ effs)
  , HFunctor (Effs (effs `Union` xeffs)))

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

-- | @`handleIO` h p@ evaluates @p@ using the handler @h@. The handler may
-- output some effects that are a subset of the IO effects and additionally
-- the program may also use a subset @xeffs@ of the IO effects (which must
-- be forwardable through the monad transformer @ts@).
-- The type argument @xeffs@ usually can't be inferred and needs given
-- explicitly.
handleIO'
  :: forall xeffs effs oeffs ts fs a
  . ( Injects oeffs IOEffects
    , ForwardsM xeffs ts
    , Monad (Apply ts IO)
    , Injects xeffs IOEffects
    , HandleIO# effs oeffs xeffs )
  => Proxy xeffs -> Handler effs oeffs ts fs
  -> Prog (effs `Union` xeffs) a -> IO (Apply fs a)
handleIO' p h = handleMFwds p ioAlg h
