{-|
Module      : Control.Effect.Internal.Effs
Description : The union type for effect operations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Internal.Effs where

import Data.Kind ( Type )
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts
import Unsafe.Coerce

import Control.Monad.ST
import Data.Array.ST
import Data.Array

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | A higher-order algebra for the union of effects @effs@ with
-- carrier being the functor @f@.
type Algebra effs f =
  forall x . Effs effs f x -> f x

-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall eff1 eff2 m .
  (Monad m, KnownNat (Length eff2))
  => (Algebra eff1 m)
  -> (Algebra eff2 m)
  -> (Algebra (eff1 :++ eff2) m)
falg # galg = heither @eff1 @eff2 (falg) (galg)

-- | @Effs effs f a@ creates a union of the effect signatures in the list @effs@.
type Effs :: [Effect] -> Effect
data Effs effs f a where
  -- | @`Effn` n op@ places an operation @n@ away from the last element of the list.
  Effn :: HFunctor eff => {-# UNPACK #-} !Int -> !(eff f a) -> Effs effs f a

-- | Matches an effect @eff@ at the head of a signature @eff ': effs@.
pattern Eff :: (HFunctor eff, KnownNat (1 + Length effs), KnownNat (Length effs))
  => eff f a -> Effs (eff ': effs) f a
pattern Eff op <- (openEff -> Just op) where
  Eff op = inj op

-- | Matches the tail @effs@ of effects of a signature @eff ': effs@.
pattern Effs :: forall eff effs f a . KnownNat (Length effs)
  => Effs effs f a -> Effs (eff ': effs) f a
pattern Effs op <- (openEffs -> Just op) where
  Effs op = unsafeCoerce @(Effs effs f a) @(Effs (eff ': effs) f a) op

-- | Weakens the signature of an operation in the union containing @effs@
-- to one that contains @eff ': effs@ for any @eff@.
{-# INLINE weakenEffs #-}
weakenEffs :: forall eff effs f a . Effs effs f a -> Effs (eff ': effs) f a
weakenEffs = unsafeCoerce @(Effs effs f a) @(Effs (eff ': effs) f a)


-- | Inspects an operation in the union @eff ': effs@ and returns the operation
-- specialied to @eff@ if possible, or a union @effs@ otherwise.
{-# INLINE open #-}
open :: forall eff effs f a . KnownNat (Length effs) => Effs (eff ': effs) f a -> Either (Effs effs f a) (eff f a)
open  eff@(Effn n op)
  | n == fromInteger (natVal' (proxy#@(Length effs))) = Right (unsafeCoerce @(_ f a) @(eff f a) op)
  | otherwise                                         = Left (unsafeCoerce @(Effs (eff ': effs) f a) @(Effs effs f a) eff)

-- | Inspects an operation in the union @eff ': effs@ and returns the operation
-- specialied to @eff@ if possible.
{-# INLINE openEff #-}
openEff :: forall eff effs f a . Member eff effs
  => Effs effs f a -> Maybe (eff f a)
openEff (Effn n op)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(eff f a) op)
  | otherwise = Nothing
  where n' = fromInteger (natVal' (proxy#@(EffIndex eff effs)))

-- | Inspects an operation in the union @eff ': effs@ and returns
-- a union @effs@ if possible.
{-# INLINE openEffs #-}
openEffs :: forall eff effs f a . KnownNat (Length effs)
  => Effs (eff ': effs) f a -> Maybe (Effs effs f a)
openEffs effn@(Effn n op)
  | n == m    = Nothing
  | otherwise = Just (unsafeCoerce @(Effs (eff ': effs) f a) @(Effs effs f a) effn)
  where m = fromInteger (natVal' (proxy#@(Length effs)))

instance Functor f => Functor (Effs effs f) where
  {-# INLINE fmap #-}
  fmap f (Effn n op) = Effn n (fmap f op)

instance HFunctor (Effs effs) where
  {-# INLINE hmap #-}
  hmap h (Effn n op) = Effn n (hmap h op)

-- | A value of type @Effs '[] f x@ cannot be created, and this is the
-- absurd destructor for this type.
{-# INLINE absurdEffs #-}
absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}

-- | Creates an alebra that can work with either signatures in @xeffs@
-- or @yeffs@ by using the provided algebras as appropriate.
{-# INLINE heither #-}
heither :: forall xeffs yeffs f a b . KnownNat (Length yeffs)
  => (Effs xeffs f a -> b) -> (Effs yeffs f a -> b) -> (Effs (xeffs :++ yeffs) f a -> b)
heither xalg yalg (Effn n op)
  | n < m     = yalg (Effn n op)
  | otherwise = xalg (Effn (n - m) op)
  where
    -- m = fromInteger (fromSNat (natSing @(Length yeffs)))
    m = fromInteger (natVal' (proxy#@(Length yeffs)))

-- | Weakens an an operation of type @Effs xeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE hinl #-}
hinl :: forall xeffs yeffs f a . KnownNat (Length yeffs)
  => Effs xeffs f a -> Effs (xeffs :++ yeffs) f a
hinl (Effn n op) = Effn (m + n) op
  where
    -- m = fromInteger (fromSNat (natSing @(Length yeffs)))
    m = fromInteger (natVal' (proxy# @(Length yeffs)))

-- | Weakens an an operation of type @Effs yeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE hinr #-}
hinr :: forall xeffs yeffs f a . Effs yeffs f a -> Effs (xeffs :++ yeffs) f a
hinr = unsafeCoerce @(Effs yeffs f a) @(Effs (xeffs :++ yeffs) f a)

-- | Attempts to project a value of type @Effs xeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE houtl #-}
houtl :: forall xeffs yeffs f a . KnownNat (Length yeffs)
  => Effs (xeffs :++ yeffs) f a -> Maybe (Effs xeffs f a)
houtl (Effn n op)
  | n < m     = Nothing
  | otherwise = Just (Effn (n - m) op)
  where
    m = fromInteger (natVal' (proxy# @(Length yeffs)))

-- | Attempts to project a value of type @Effs yeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE houtr #-}
houtr :: forall xeffs yeffs f a . KnownNat (Length yeffs)
  => Effs (xeffs :++ yeffs) f a -> Maybe (Effs yeffs f a)
houtr effn@(Effn n op)
  | n < m     = Just (unsafeCoerce @(Effs (xeffs :++ yeffs) f a) @(Effs yeffs f a) effn)
  | otherwise = Nothing
  where
    m = fromInteger (natVal' (proxy# @(Length yeffs)))

-- | Weakens an algera that works on @xyeffs@ to work on @xeffs@ when
-- every effect in @xeffs@ is in @xyeffs@.
{-# INLINE weakenAlg #-}
weakenAlg
  :: forall xeffs xyeffs m x . (Injects xeffs xyeffs)
  => (Effs xyeffs m x -> m x)
  -> (Effs xeffs  m x -> m x)
weakenAlg alg = alg . injs

-- | Constructs an operation in the union @Effs effs f a@ from a single
-- operation @eff f a@, when @eff@ is in @effs@.
{-# INLINE inj #-}
inj :: forall eff effs f a . (HFunctor eff, Member eff effs) => eff f a -> Effs effs f a
inj = Effn n
  where
    n = fromInteger (natVal' (proxy# @(EffIndex eff effs)))

-- | Attempts to project an operation of type @eff f a@ from a the union @Effs effs f a@,
-- when @eff@ is in @effs@.
{-# INLINE prj #-}
prj :: forall eff effs f a . (Member eff effs)
  => Effs effs f a -> Maybe (eff f a)
prj (Effn n x)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(eff f a) x)
  | otherwise = Nothing
  where
    n' = fromInteger (natVal' (proxy# @(EffIndex eff effs)))

-- | Injects xeffs yeffs means that all of xeffs is in xyeffs
-- Some other effects may be in xyeffs, so xeffs <= yeffs
class KnownNat (Length xeffs) => Injects xeffs xyeffs where
  injs :: Effs xeffs f a -> Effs xyeffs f a
  ixs :: Array Int Int

instance (KnownNats (EffIndexes xeffs xyeffs), KnownNat (Length xeffs))
  => Injects xeffs xyeffs where
  {-# INLINE injs #-}
  injs (Effn n op) = Effn (ixs @xeffs @xyeffs ! n) op

  {-# INLINE ixs #-}
  ixs = runSTArray $ do arr <- newArray_ (0, m - 1)
                        natVals (proxy# :: Proxy# (EffIndexes xeffs xyeffs)) arr
                        return arr
    where
      m = fromInteger (natVal' (proxy# :: Proxy# (Length xeffs)))

-- | Constructs an algebra for the union containing @xeffs `Union` yeffs@
-- by using an algebra for the union @xeffs@ and aonther for the union @yeffs@.
{-# INLINE hunion #-}
hunion :: forall xeffs yeffs f a b . Injects (yeffs :\\ xeffs) yeffs
  => (Effs xeffs f a -> b) -> (Effs yeffs f a -> b)
  -> (Effs (xeffs `Union` yeffs) f a -> b)
hunion xalg yalg = heither @xeffs @(yeffs :\\ xeffs) xalg (yalg . injs)

-- | @`EffIndex` eff effs@ finds the index of @eff@ in @effs@, where
-- the last element has index @0@, and the head element has index @Length effs - 1@.
type family EffIndex (eff :: a) (effs :: [a]) :: Nat where
  EffIndex eff (eff ': effs) = Length effs
  EffIndex eff (_ ': effs) = EffIndex eff effs

-- | Given @xeffs@ which is a subset of effects in @yeffs@, @`EffIndexes` xeffs
-- yeffs@ finds the index @`EffIndex` eff yeffs@ for each @eff@ in @xeffs@, and
-- returns this as a list of indices.
type family EffIndexes (xeffs :: [a]) (yeffs :: [a]) :: [Nat] where
  EffIndexes '[] yeffs       = '[]
  EffIndexes (eff ': xeffs) yeffs = EffIndex eff yeffs ': EffIndexes xeffs yeffs

-- | A class that witnesses that all the type level nats @ns@ can be reflected
-- into a value level list. Indexing starts from the end of the list, so that
-- the last element always has index @0@.
class KnownNat (Length ns) => KnownNats (ns :: [Nat]) where
  natVals :: Proxy# ns -> STArray s Int Int -> ST s ()

instance KnownNats '[] where
  {-# INLINE natVals #-}
  natVals _ _ = return ()

instance (KnownNat x, KnownNats xs, KnownNat (Length (x ': xs))) => KnownNats (x ': xs) where
  {-# INLINE natVals #-}
  natVals _ arr = do writeArray arr (fromInteger $ natVal' (proxy# @(Length xs)))
                                    (fromInteger $ natVal' (proxy# @x))
                     natVals (proxy# :: Proxy# xs) arr

-- | @Member eff effs@ holds when @eff@ is contained in @effs@.
type Member :: Effect -> [Effect] -> Constraint
type Member eff effs = (KnownNat (EffIndex eff effs))

-- | @Member effs effs'@ holds when every @eff@ which is a 'Member' of in @effs@
-- is also a 'Member' of @effs'@.
type family Members (xeffs :: [Effect]) (xyeffs :: [Effect]) :: Constraint where
  Members '[] xyeffs       = ()
  Members (xeff ': xeffs) xyeffs = (Member xeff xyeffs, Members xeffs xyeffs)
