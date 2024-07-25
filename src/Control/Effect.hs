module Control.Effect
  ( Prog
  , Progs
  , call
  , weakenProg
  , eval
  , fold

  , Effs (Eff, Effs)
  , Member(..)
  , Members(..)
  , prj
  , inj

  , Algebra
  , (#)
  , Forward (..)
  , Forwards (..)

  , Handler (..)
  , Injects (..)
  , handler
  , handle
  , handleM
  , interpret
  , interpretM
  , identity
  , fuse, (|>)
  , pipe, (||>)
  , hide
  , Apply
  , HApply

  , Compose(..)
  , Identity(..)
  , ComposeT(..)
  , IdentityT(..)
  ) where

import Data.Functor.Identity
import Data.Functor.Compose
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Handler
import Control.Effect.Internal.Forward
