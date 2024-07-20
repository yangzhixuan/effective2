{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Type
  ( Signature
  , Effect
  , Algebra
  , Effs
  , pattern Eff
  , pattern Effs
  , absurdEffs
  , weakenAlg
  , Injects (..)
  , Member (..)
  , inj
  , prj
  , Members
  , hunion
  , heither
  , hinl, hinr
  , houtl, houtr
  , KnownNat
  )

 where

import Data.Kind ( Type )
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts
import Unsafe.Coerce

type Signature = Type -> Type
type Effect = (Type -> Type) -> (Type -> Type)

type Algebra effs f =
  forall x . Effs effs f x -> f x

-- `Effn n op` places an operation `n` away from the last element of the list.
type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Effn :: HFunctor sig => {-# UNPACK #-} !Int -> !(sig f a) -> Effs sigs f a

pattern Eff :: (HFunctor sig, KnownNat (1 + Length sigs), KnownNat (Length sigs)) => sig f a -> Effs (sig ': sigs) f a
pattern Eff op <- (openEff -> Just op) where
  Eff op = inj op

pattern Effs :: KnownNat (Length sigs) => Effs sigs f a -> Effs (sig ': sigs) f a
pattern Effs op <- (openEffs -> Just op) where
  Effs op = unsafeCoerce op

{-# INLINE weakenEffs #-}
weakenEffs :: Effs sigs f a -> Effs (sig ': sigs) f a
weakenEffs = unsafeCoerce

{-# INLINE open #-}
open :: forall sig sigs f a . KnownNat (Length sigs) => Effs (sig ': sigs) f a -> Either (Effs sigs f a) (sig f a)
open  eff@(Effn n op)
  | n == fromInteger (fromSNat (natSing @(Length sigs))) = Right (unsafeCoerce op)
  | otherwise                                            = Left (unsafeCoerce eff)


{-# INLINE openEff #-}
openEff :: forall sig sigs f a . Member sig sigs
  => Effs sigs f a -> Maybe (sig f a)
openEff (Effn n op)
  | n == n'   = Just (unsafeCoerce op)
  | otherwise = Nothing
  where n' = fromInteger (fromSNat (natSing @(EffIndex sig sigs)))

{-# INLINE openEffs #-}
openEffs :: forall sig sigs f a . KnownNat (Length sigs)
  => Effs (sig ': sigs) f a -> Maybe (Effs sigs f a)
openEffs effn@(Effn n op)
  | n == m    = Nothing
  | otherwise = Just (unsafeCoerce effn)
  where
    m = fromInteger (fromSNat (natSing @(Length sigs)))

instance Functor f => Functor (Effs sigs f) where
  fmap f (Effn n op) = Effn n (fmap f op)

instance HFunctor (Effs sigs) where
  hmap h (Effn n op) = Effn n (hmap h op)

{-# INLINE absurdEffs #-}
absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}

{-# INLINE heither #-}
heither :: forall xs ys f a b . KnownNat (Length ys)
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs :++ ys) f a -> b)
heither xalg yalg (Effn n op)
  | n < m     = yalg (Effn n op)
  | otherwise = xalg (Effn (n - m) op)
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE hinl #-}
hinl :: forall xs ys f a . KnownNat (Length ys)
  => Effs xs f a -> Effs (xs :++ ys) f a
hinl (Effn n op) = Effn (m + n) op
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE hinr #-}
hinr :: Effs ys f a -> Effs (xs :++ ys) f a
hinr = unsafeCoerce

{-# INLINE houtl #-}
houtl :: forall xs ys f a . KnownNat (Length ys)
  => Effs (xs :++ ys) f a -> Maybe (Effs xs f a)
houtl (Effn n op)
  | n < m     = Nothing
  | otherwise = Just (Effn (n - m) op)
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE houtr #-}
houtr :: forall xs ys f a . KnownNat (Length ys)
  => Effs (xs :++ ys) f a -> Maybe (Effs ys f a)
houtr effn@(Effn n op)
  | n < m     = Just (unsafeCoerce effn)
  | otherwise = Nothing
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE weakenAlg #-}
weakenAlg
  :: forall eff eff' m x . (Injects eff eff')
  => (Effs eff' m x -> m x)
  -> (Effs eff  m x -> m x)
weakenAlg alg = alg . injs

type Member :: Effect -> [Effect] -> Constraint
type Member sig sigs = (KnownNat (EffIndex sig sigs))

{-# INLINE inj #-}
inj :: forall sig sigs f a . (HFunctor sig, Member sig sigs) => sig f a -> Effs sigs f a
inj = Effn n
  where
    n = fromInteger (fromSNat (natSing @(EffIndex sig sigs)))

{-# INLINE prj #-}
prj :: forall sig sigs f a . (Member sig sigs)
  => Effs sigs f a -> Maybe (sig f a)
prj (Effn n x)
  | n == n'   = Just (unsafeCoerce x)
  | otherwise = Nothing
  where
    n' = fromInteger (fromSNat (natSing @(EffIndex sig sigs)))

type family Members (xs :: [Effect]) (xys :: [Effect]) :: Constraint where
  Members '[] xys       = ()
  Members (x ': xs) xys = (Member x xys, Members xs xys, Injects (x ': xs) xys)

-- Injects xs ys means that all of xs is in xys
-- Some other effects may be in xys, so xs <= ys
type  Injects :: [Effect] -> [Effect] -> Constraint
class Injects xs xys where
  injs :: Effs xs f a -> Effs xys f a

instance Injects '[] xys where
  {-# INLINE injs #-}
  injs :: Effs '[] f a -> Effs xys f a
  injs = absurdEffs

instance (KnownNat (Length xs), KnownNat (Length (x ': xs)), Member x xys, Injects xs xys, HFunctor x)
  => Injects (x ': xs) xys where
  {-# INLINE injs #-}
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

-- extract the effect from list of xeffs using the natural,
-- and inject it back into yeffs if it is present there
-- injs' :: ElemIndexes xeffs yeffs => Effs xeffs f a -> Effs yeffs f a
-- injs' (Effn n op) = undefined

{-# INLINE hunion #-}
hunion :: forall xs ys f a b
  . ( Injects (ys :\\ xs) ys, KnownNat (Length xs), KnownNat (Length (ys :\\ xs)) )
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs `Union` ys) f a -> b)
hunion xalg yalg = heither @xs @(ys :\\ xs) xalg (yalg . injs)

type family EffIndex (x :: a) (xs :: [a]) :: Nat where
  EffIndex x (x ': xs) = Length xs
  EffIndex x (_ ': xs) = EffIndex x xs