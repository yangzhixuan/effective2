{-|
Module      : Control.Effect.Nondet
Description : Effects for the nondeterminism
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides access to stateful operations and handlers.
The implementation uses strict state by default, offered by "Control.Effect.State.Strict".
For lazy state, import "Control.Effect.State.Lazy" instead.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Nondet
  ( Choose
  , Choose_(Choose_)
  , Nondet
  , Empty
  , Empty_(Empty_)
  , Once
  , Once_ (..)
  , ListT (..)
  , select
  , selects
  , once
  , list
  , nondet
  , nondet'
  , backtrack
  , backtrackAlg
  , backtrackOnceAlg
  , Control.Applicative.Alternative(..)
  ) where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Nondet.Type
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Effect.Alternative
import Control.Applicative
import Control.Monad.Trans.List
-- import Control.Effect.Nondet.Logic
import Control.Effect.Alternative


import Control.Effect.Nondet.List
