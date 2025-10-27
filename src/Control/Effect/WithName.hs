{-# LANGUAGE GeneralizedNewtypeDeriving, QuantifiedConstraints, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, AllowAmbiguousTypes #-}
{-|
Module      : Control.Effect.WithName
Description : Making copies of existing effects with names
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides an \'imitater\' effect that clones an existing effect.
The effect @WithName name eff@ is simply a newtype wrapper of @eff@, so the
existing handlers of @eff@ can be transported to be handlers of @WithName name eff@.
A typical use case of this effect is for having multiple instances of mutable state.
-}
module Control.Effect.WithName (
  -- * Syntax
  WithName (..),
  (:@),
  Rename,
  RenameAll,

  -- * Semantics
  renameEff, renameEffAT,
  renameOEff, renameOEffAT,
  renameEffs, renameEffsAT,
  renameOEffs, renameOEffsAT,
  renameIOEffs, renameIOEffsAT,
  callWithName,
  callWithNameAlg,
  callWithNameScp,
) where

import Control.Effect
import Data.List.Kind
import Data.HFunctor
import Unsafe.Coerce
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Data.Kind (Type)
import GHC.Base (Symbol)

import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.Runner

-- | Make a copy of an effect signature and attach a name to it.
-- This is useful when more than one instances of the same effect
-- are needed in a program.
newtype WithName
  (name :: Symbol)
  (eff  :: Effect)
  (f    :: Type -> Type)
  (k    :: Type)
  = WithName { unWithName :: eff f k } deriving (Functor, HFunctor)

-- A binary operator for @WithName@
type (:@) :: Symbol -> Effect -> Effect
type name :@ eff = WithName name eff

instance Forward eff t => Forward (WithName name eff) t where
  type FwdConstraint (WithName name eff) t = FwdConstraint eff t
  fwd alg (WithName op) = fwd (alg . WithName) op

-- | @Rename name eff effs@ replaces (the first occurrence of) @eff@ in @effs@ with @WithName name eff@.
type family Rename (name :: Symbol) (eff :: Effect) (effs :: [Effect]) :: [Effect] where
  Rename name eff '[]            = '[]
  Rename name eff (eff : effs')  = WithName name eff : effs'
  Rename name eff (eff' : effs') = eff' : Rename name eff effs'

-- | @RenameAll name effs@ tags every effect in @effs@ with the name @name@.
type family RenameAll (name :: Symbol) (effs :: [Effect]) :: [Effect] where
  RenameAll name '[] = '[]
  RenameAll name (eff : effs') = WithName name eff : RenameAll name effs'

-- | Rename a single member in the input effects.
--
-- The implementation is based on unsafe coercision but it is actually safe because
-- @Effs effs f x@ and @Effs (Rename name eff effs) f x@ will always have the exactly
-- the same representation, although GHC doesn't see this.
renameEff :: Proxy name -> Proxy eff -> Handler effs oeffs ts fs
          -> Handler (Rename name eff effs) oeffs ts fs
renameEff p q = unsafeCoerce

-- | Rename all input effects.
renameEffs :: Proxy name -> Handler effs oeffs ts fs
           -> Handler (RenameAll name effs) oeffs ts fs
renameEffs p = unsafeCoerce

-- | Rename a single member in the output effects.
renameOEff :: Proxy name -> Proxy eff -> Handler effs oeffs ts fs
           -> Handler effs (Rename name eff oeffs) ts fs
renameOEff p q = unsafeCoerce

-- | Rename all output effects.
renameOEffs :: Proxy name -> Handler effs oeffs ts fs
            -> Handler effs (RenameAll name oeffs) ts fs
renameOEffs p = unsafeCoerce

-- | Rename all input and output effects.
renameIOEffs :: Proxy name -> Handler effs oeffs ts fs
             -> Handler (RenameAll name effs) (RenameAll name oeffs) ts fs
renameIOEffs p = unsafeCoerce

renameEffAT :: Proxy name -> Proxy eff -> AlgTrans effs oeffs ts cs
            -> AlgTrans (Rename name eff effs) oeffs ts cs
renameEffAT p q = unsafeCoerce

-- | Rename all input effects.
renameEffsAT :: Proxy name -> AlgTrans effs oeffs ts cs
           -> AlgTrans (RenameAll name effs) oeffs ts cs
renameEffsAT p = unsafeCoerce

-- | Rename a single member in the output effects.
renameOEffAT :: Proxy name -> Proxy eff -> AlgTrans effs oeffs ts cs
           -> AlgTrans effs (Rename name eff oeffs) ts cs
renameOEffAT p q = unsafeCoerce

-- | Rename all output effects.
renameOEffsAT :: Proxy name -> AlgTrans effs oeffs ts cs
            -> AlgTrans effs (RenameAll name oeffs) ts cs
renameOEffsAT p = unsafeCoerce

-- | Rename all input and output effects.
renameIOEffsAT :: Proxy name -> AlgTrans effs oeffs ts cs
             -> AlgTrans (RenameAll name effs) (RenameAll name oeffs) ts cs
renameIOEffsAT p = unsafeCoerce

-- Call an operation with a given name. The name parameger typically needs to be
-- passed explicitly.
callWithName :: forall name eff effs a . (HFunctor eff, Member (WithName name eff) effs)
      => eff (Prog effs) a -> Prog effs a
callWithName x = call (WithName @name x)

-- | Special case of `callWithName` for algebraic operations
callWithNameAlg :: forall name f effs a. (Member (WithName name (Alg f)) effs, Functor f)
                => f a -> Prog effs a
callWithNameAlg f = callWithName @name (Alg f)

-- | Special case of `callWithName` for scoped operations
callWithNameScp :: forall name f effs a. (Member (WithName name (Scp f)) effs, Functor f) 
                => f (Prog effs a) -> Prog effs a
callWithNameScp f = callWithName @name (Scp f)