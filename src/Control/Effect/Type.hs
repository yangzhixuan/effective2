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

type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Effn :: HFunctor sig => !Int -> sig f a -> Effs sigs f a

pattern Eff :: HFunctor sig => sig f a -> Effs (sig ': sigs) f a
pattern Eff op <- (open -> Right op) where
  Eff op = inj op

pattern Effs :: Effs sigs f a -> Effs (sig ': sigs) f a
pattern Effs op <- (open -> Left op) where
  Effs op = weakenEffs op

{-# INLINE weakenEffs #-}
weakenEffs :: Effs sigs f a -> Effs (sig ': sigs) f a
weakenEffs (Effn n op) = Effn (n + 1) op

{-# INLINE open #-}
open :: Effs (sig ': sigs) f a -> Either (Effs sigs f a) (sig f a)
open (Effn 0 op) = Right (unsafeCoerce op)
open (Effn n op) = Left  (Effn (n - 1) op)


instance Functor f => Functor (Effs sigs f) where
--  fmap f (Eff x)  = Eff (fmap f x)
--  fmap f (Effs x) = Effs (fmap f x)
  fmap f (Effn n op) = Effn n (fmap f op)

instance HFunctor (Effs sigs) where
--  hmap h (Eff x)  = Eff (hmap h x)
--  hmap h (Effs x) = Effs (hmap h x)
  hmap h (Effn n op) = Effn n (hmap h op)

{-# INLINE absurdEffs #-}
absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}

{-# INLINE heither #-}
heither :: forall xs ys f a b . KnownNat (Length xs)
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs :++ ys) f a -> b)
heither xalg yalg (Effn n op)
  | n < m     = xalg (Effn n op)
  | otherwise = yalg (Effn (n - m) op)
  where
    m = fromInteger (natVal' (proxy# :: Proxy# (Length xs)))

{-# INLINE hinl #-}
hinl :: forall xs ys f a . Effs xs f a -> Effs (xs :++ ys) f a
hinl (Effn n op) = Effn n op

{-# INLINE hinr #-}
hinr :: forall xs ys f a . KnownNat (Length xs)
  => Effs ys f a -> Effs (xs :++ ys) f a
hinr (Effn n op) = (Effn (m + n) op)
  where
    m = fromInteger (natVal' (proxy# :: Proxy# (Length xs)))

{-# INLINE houtl #-}
houtl :: forall xs ys f a . KnownNat (Length xs)
  => Effs (xs :++ ys) f a -> Maybe (Effs xs f a)
houtl (Effn n op)
  | n < m     = Just (Effn n op)
  | otherwise = Nothing
  where
    m = fromInteger (natVal' (proxy# :: Proxy# (Length xs)))

{-# INLINE houtr #-}
houtr :: forall xs ys f a . KnownNat (Length xs)
  => Effs (xs :++ ys) f a -> Maybe (Effs ys f a)
houtr (Effn n op)
  | n < m     = Nothing
  | otherwise = Just (Effn (n - m) op)
  where
    m = fromInteger (natVal' (proxy# :: Proxy# (Length xs)))

{-# INLINE weakenAlg #-}
weakenAlg
  :: forall eff eff' m x . (Injects eff eff')
  => (Effs eff' m x -> m x)
  -> (Effs eff  m x -> m x)
weakenAlg alg = alg . injs

type Member :: Effect -> [Effect] -> Constraint
-- type Member sig sigs = Member' sig sigs (ElemIndex sig sigs)
type Member sig sigs = KnownNat (ElemIndex sig sigs)

{-# INLINE inj #-}
inj :: forall sig sigs f a . (HFunctor sig, Member sig sigs) => sig f a -> Effs sigs f a
inj = inj' (fromInteger (natVal' (proxy# :: Proxy# (ElemIndex sig sigs :: Nat))))

{-# INLINE prj #-}
prj :: forall sig sigs f a . Member sig sigs => Effs sigs f a -> Maybe (sig f a)
prj = prj' (fromInteger (natVal' (proxy# :: Proxy# (ElemIndex sig sigs :: Nat))))

{-# INLINE inj' #-}
inj' :: forall sig sigs f a . HFunctor sig => Int -> sig f a -> Effs sigs f a
inj' = Effn

{-# INLINE prj' #-}
prj' :: forall sig sigs f a . Int -> Effs sigs f a -> Maybe (sig f a)
prj' m (Effn n x)
  | m == n    = Just (unsafeCoerce x)
  | otherwise = Nothing

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

instance (Member x xys, Injects xs xys, HFunctor x)
  => Injects (x ': xs) xys where
  {-# INLINE injs #-}
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

{-# INLINE hunion #-}
hunion :: forall xs ys f a b
  . ( Injects (ys :\\ xs) ys, KnownNat (Length xs) )
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs `Union` ys) f a -> b)
hunion xalg yalg = heither @xs @(ys :\\ xs) xalg (yalg . injs)