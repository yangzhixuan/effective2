{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Type where

import Data.Kind ( Type, Constraint )
import Data.HFunctor
import Data.List.Kind

type Signature = Type -> Type
type Effect = (Type -> Type) -> (Type -> Type)

type Algebra effs f =
   forall x . Effs effs f x -> f x

type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Eff  :: HFunctor sig => sig f a -> Effs (sig ': sigs) f a
  Effs :: Effs sigs f a -> Effs (sig ': sigs) f a

instance Functor f => Functor (Effs sigs f) where
  fmap f (Eff x)  = Eff (fmap f x)
  fmap f (Effs x) = Effs (fmap f x)

instance HFunctor (Effs sigs) where
  hmap h (Eff x)  = Eff (hmap h x)
  hmap h (Effs x) = Effs (hmap h x)

absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}

type  Append :: [Effect] -> [Effect] -> Constraint
class Append xs ys where
  heither :: (Effs xs h a -> b) -> (Effs ys h a -> b) -> (Effs (xs :++ ys) h a -> b)

  hinl :: Effs xs f a -> Effs (xs :++ ys) f a
  hinr :: Effs ys f a -> Effs (xs :++ ys) f a

  houtl :: Effs (xs :++ ys) f a -> Maybe (Effs xs f a)
  houtr :: Effs (xs :++ ys) f a -> Maybe (Effs ys f a)

instance Append '[] ys where
  heither :: (Effs '[] f a -> b) -> (Effs ys f a -> b) -> (Effs ('[] :++ ys) f a -> b)
  heither xalg yalg = yalg

  hinl :: Effs '[] f a -> Effs ys f a
  hinl = absurdEffs

  hinr :: Effs ys f a -> Effs ys f a
  hinr = id

  houtl :: Effs ys f a -> Maybe (Effs '[] f a)
  houtl = const Nothing

  houtr :: Effs ys f a -> Maybe (Effs ys f a)
  houtr = Just

instance Append xs ys => Append (x ': xs) ys where
  heither :: (Effs (x : xs) f a -> b) -> (Effs ys f a -> b) -> Effs ((x : xs) :++ ys) f a -> b
  heither xalg yalg (Eff x)  = xalg (Eff x)
  heither xalg yalg (Effs x) = heither (xalg . Effs) yalg x

  hinl :: Effs (x : xs) f a -> Effs ((x : xs) :++ ys) f a
  hinl (Eff x)  = Eff x
  hinl (Effs x) = Effs (hinl @xs @ys x)

  hinr :: Effs ys f a -> Effs ((x : xs) :++ ys) f a
  hinr = Effs . hinr @xs @ys

  houtl :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs (x ': xs) f a)
  houtl (Eff x)  = Just (Eff x)
  houtl (Effs x) = fmap Effs (houtl @xs @ys x)

  houtr :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs ys f a)
  houtr (Eff x)  = Nothing
  houtr (Effs x) = houtr @xs @ys x