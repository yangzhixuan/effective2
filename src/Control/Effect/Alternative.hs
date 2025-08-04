{-|
Module      : Control.Effect.Alternative
Description : Effects for alternatives with choose and empty
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}

module Control.Effect.Alternative (
  -- * Syntax
  -- ** Operations

  -- | The operations for alternatives use 'empty' and '<|>' directly
  -- from the 'Control.Applicative.Alternative' type class.
  --
  -- 'empty' is an algebraic operation:
  --
  -- > empty >>= k = empty
  --
  -- '<|>' is a scoped operation.
  empty,
  (<|>),

  -- ** Signatures
  Empty, Empty_(..),
  Choose, Choose_(..),

  -- * Semantics
  -- ** Handlers
  alternative,

  -- ** Algebras
  alternativeAT,
  alternativeAlg,
) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Applicative

-- | Instance for 'Alternative' that uses 'Empty' and 'Choose'.
instance (Member Empty sigs, Member Choose sigs)
  => Alternative (Prog sigs) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty :: Member Empty sigs => Prog sigs a
  empty = call (Alg Empty_)

  {-# INLINE (<|>) #-}
-- | Syntax for a choice of alternatives. This is a scoped operation.
  (<|>) :: (Member Choose sigs) => Prog sigs a -> Prog sigs a -> Prog sigs a
  xs <|> ys = call (Scp (Choose_ xs ys))

-- | Signature for empty alternatives.
type Empty = Alg Empty_
-- | Underlying signature for empty alternatives.
data Empty_ a where
  Empty_ :: Empty_ a
  deriving Functor

pattern Empty :: Member Empty effs => Effs effs m k
pattern Empty <- (prj -> Just (Alg Empty_))
  where Empty = inj (Alg Empty_)

-- | Signature for choice of alternatives.
type Choose = Scp Choose_
-- type Choose = Alg Choose_
-- | Underlying signature for choice of alternatives.
data Choose_ a where
  Choose_ :: a -> a -> Choose_ a
  deriving Functor

pattern Choose :: Member Choose effs => m k -> m k -> Effs effs m k
pattern Choose x y <- (prj -> Just (Scp (Choose_ x y )))
  where Choose x y = inj (Scp (Choose_ x y))

-- | The 'alternative' handler makes use of an 'Alternative' functor @f@
-- as well as a transformer @t@ that produces an 'Alternative' functor @t m@.
-- for any monad @m@ to provide semantics.
{-# INLINE alternative #-}
alternative
  :: forall t f
  .  (forall m . Monad m => Alternative (t m))
  => (forall m . Monad m => (forall a . t m a -> m (f a)))
  -> Handler '[Empty, Choose] '[] '[t] '[f]
alternative run = handler' run alternativeAlg

-- | An alternative definition of `alternative`.
alternative'
  :: forall t f
  .  (forall m . Monad m => Alternative (t m))
  => (forall m . Monad m => (forall a . t m a -> m (f a)))
  -> Handler '[Empty, Choose] '[] '[t] '[f]
alternative' run =  emptyAlgT #: chooseAlgT #: runner run

-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
alternativeAT
  :: forall t. (forall m . Monad m => Alternative (t m))
  => AlgTrans '[Empty, Choose] '[] '[t] Monad
alternativeAT = AlgTrans alternativeAlg

{-# INLINE alternativeAlg #-}
alternativeAlg
  :: forall oeffs t . (forall m . Monad m => Alternative (t m))
  => forall m. Monad m
  => Algebra oeffs m -> Algebra [Empty, Choose] (t m)
alternativeAlg oalg eff
  | (Just (Alg Empty_))          <- prj eff = empty
  | (Just (Scp (Choose_ xs ys))) <- prj eff = xs <|> ys

emptyAlgT :: forall t. (forall m . Monad m => Alternative (t m))
  => AlgTrans '[Empty] '[] '[t] Monad
-- emptyAlgT = AlgTrans (const emptyAlg)
emptyAlgT = algTrans1 (\oalg ((Alg Empty_)) -> empty)

emptyAlg :: Alternative (t m) => Algebra '[Empty] (t m)
emptyAlg (Eff (Alg (Empty_))) = empty

chooseAlgT :: forall t. (forall m . Monad m => Alternative (t m))
  => AlgTrans '[Choose] '[] '[t] Monad
-- chooseAlgT = AlgTrans (\oalg (Eff (Scp (Choose xs ys))) -> xs <|> ys)
-- chooseAlgT = AlgTrans (\oalg (prj -> Just (Scp (Choose xs ys))) -> xs <|> ys)
chooseAlgT = algTrans1 (\oalg ((Scp (Choose_ xs ys))) -> xs <|> ys)

chooseAlg :: Alternative (t m) => Algebra '[Choose] (t m)
chooseAlg (Eff (Scp (Choose_ xs ys))) = xs <|> ys

