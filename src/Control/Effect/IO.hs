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
  io, getLine, putStrLn, putStr, getCPUTime,

  -- ** Signatures
  IOEffects, IOAlgOps,
  GetLine, GetLine_(..),
  PutStrLn, PutStrLn_(..),
  PutStr, PutStr_(..),
  GetCPUTime, GetCPUTime_(..),

  -- * Semantics
  -- * Evaluation
  evalIO,
  handleIO,
  handleIO',

  -- * Algebras
  ioAlgAlg,
  ioAlg,
  nativeAlg,
  putStrLnAlg,
  putStrAlg,
  getLineAlg,
  getCPUTimeAlg,
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

import qualified System.CPUTime
import qualified Control.Concurrent
import qualified Control.Concurrent.MVar as MVar
import Data.List.Kind
import Data.HFunctor

import Prelude hiding (getLine, putStrLn, putStr)
import qualified Prelude as Prelude

-- | The algebraic operations that the IO monad supports natively
type IOAlgOps = '[ Alg IO
                  , GetLine
                  , PutStrLn
                  , PutStr
                  , GetCPUTime
                  ]

-- | All effectful operations that the IO monad supports natively
type IOEffects = IOAlgOps :++ '[Par, JPar]

-- | Interprets IO algebraic operations using their standard semantics in `IO`.
ioAlgAlg :: Algebra IOAlgOps IO
ioAlgAlg = nativeAlg # getLineAlg # putStrLnAlg # putStrAlg # getCPUTimeAlg

-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra IOEffects IO
ioAlg = ioAlgAlg # parAlg # jparAlg

-- | Treating an IO computation as an operation of signature `Alg IO`.
io :: Members '[Alg IO] sig => IO a -> Prog sig a
io o = call (Alg o)

-- | Algebra for the generic algebraic IO effect
nativeAlg :: Algebra '[Alg IO] IO
nativeAlg op
  | Just (Alg (op')) <- prj op = op'

-- | Signature for `Control.Effects.IO.getLine`.
type GetLine = Alg GetLine_
-- | Underlying signature for `Control.Effects.IO.getLine`.
data GetLine_ k  = GetLine (String -> k) deriving Functor

-- | Read a line from from standard input device.
getLine :: Members '[GetLine] sig => Prog sig String
getLine = call (Alg (GetLine id))

-- | Signature for `Control.Effect.IO.putStrLn`.
type PutStrLn = Alg PutStrLn_
-- | Underlying signature for `Control.Effect.IO.putStrLn`.
data PutStrLn_ k = PutStrLn String k     deriving Functor

-- | Write a string to the standard output device, and add a newline character.
putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = call (Alg (PutStrLn str ()))

-- | Signature for `Control.Effect.IO.putStr`.
type PutStr = Alg PutStr_
-- | Underlying signature for `Control.Effect.IO.putStr`.
data PutStr_ k = PutStr String k     deriving Functor

-- | Write a string to the standard output device.
putStr :: Members '[PutStr] sig => String -> Prog sig ()
putStr str = call (Alg (PutStr str ()))

-- | Signature for `Control.Effect.IO.getCPUTime`.
type GetCPUTime = Alg (GetCPUTime_)
-- | Underlying signature for `Control.Effect.IO.getCPUTime`.
data GetCPUTime_ k = GetCPUTime (Integer -> k) deriving Functor

-- | Returns the number of picoseconds CPU time used by the current
-- program.
getCPUTime :: Members '[GetCPUTime] sig => Prog sig Integer
getCPUTime = call (Alg (GetCPUTime id))

-- | Interprets `Control.Effects.IO.getLine` using `Prelude.getLine` from "Prelude".
getLineAlg :: Algebra '[GetLine] IO
getLineAlg eff
  | Just (Alg (GetLine x)) <- prj eff =
      do str <- Prelude.getLine
         return (x str)

-- | Interprets `Control.Effect.IO.putStrLn` using `Prelude.putStrLn` from "Prelude".
putStrLnAlg :: Algebra '[PutStrLn] IO
putStrLnAlg eff
  | Just (Alg (PutStrLn str x)) <- prj eff =
      do Prelude.putStrLn str
         return x

-- | Interprets `Control.Effect.IO.putStr` using `Prelude.putStr` from "Prelude".
putStrAlg :: Algebra '[PutStr] IO
putStrAlg eff
  | Just (Alg (PutStr str x)) <- prj eff =
      do Prelude.putStr str
         return x

-- | Interprets `Control.Effect.IO.getCPUTime` using `System.CPUTime.getCPUTime` from "System.CPUTime".
getCPUTimeAlg :: Algebra '[GetCPUTime] IO
getCPUTimeAlg eff
  | Just (Alg (GetCPUTime x)) <- prj eff =
      do time <- System.CPUTime.getCPUTime
         return (x time)

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

-- | @`handleIO` h p@ evaluates @p@ using the handler @h@. The handler may
-- output some effects that are a subset of the IO effects and additionally
-- the program may also use a subset @xeffs@ of the IO effects (which must
-- be forwardable through the monad transformer @ts@).
-- The type argument @xeffs@ usually can't be inferred and needs given
-- explicitly.
handleIO
  :: forall xeffs effs oeffs ts fs a
  . ( Injects oeffs IOEffects
    , ForwardsM xeffs ts
    , Monad (Apply ts IO)
    , Injects xeffs IOEffects
    , HandleIO# effs oeffs xeffs )
  => Proxy xeffs -> Handler effs oeffs ts fs
  -> Prog (effs `Union` xeffs) a -> IO (Apply fs a)
handleIO p h = handleMFwds p ioAlg h

-- | @`handleIO'` h p@ evaluates @p@ using the handler @h@. Any residual
-- effects are then interpreted in `IO` using their standard semantics, but
-- IO effects are not forwarded along the handler.
handleIO'
  :: forall effs oeffs ts fs a
  . ( Injects oeffs IOEffects
    , Monad (Apply ts IO)
    , HFunctor (Effs effs) )
  => Handler effs oeffs ts fs
  -> Prog effs a -> IO (Apply fs a)
handleIO' = handleM' @effs @oeffs ioAlg