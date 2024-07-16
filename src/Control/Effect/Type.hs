{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Type where

import Data.Kind ( Type, Constraint )
import Data.HFunctor
import Data.List.Kind
import Data.Proxy
import Data.Nat

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

{-# INLINE weakenAlg #-}
weakenAlg
  :: forall eff eff' m x . (Injects eff eff')
  => (Effs eff' m x -> m x)
  -> (Effs eff  m x -> m x)
weakenAlg alg = alg . injs

class (HFunctor sig, HFunctor (Effs sigs)) => Member' sig sigs (n :: Nat) where
  inj' :: Proxy n -> sig f a -> Effs sigs f a
  prj' :: Proxy n -> Effs sigs f a -> Maybe (sig f a)


instance (HFunctor sig, (sigs' ~ (sig ': sigs))) => Member' sig sigs' Z where
  {-# INLINE inj' #-}
  inj' :: (HFunctor sig, sigs' ~ (sig : sigs)) => Proxy Z -> sig f a -> Effs sigs' f a
  inj' _ x = Eff x

  {-# INLINE prj' #-}
  prj' :: (HFunctor sig, sigs' ~ (sig : sigs)) => Proxy Z -> Effs sigs' f a -> Maybe (sig f a)
  prj' _ (Eff x) = Just x
  prj' _ _       = Nothing

instance (sigs' ~ (sig' ': sigs), HFunctor sig, Member' sig sigs n) => Member' sig sigs' (S n) where
  {-# INLINE inj' #-}
  inj' _ x = Effs . inj' (Proxy :: Proxy n) $ x

  {-# INLINE prj' #-}
  prj' _ (Eff _)  = Nothing
  prj' _ (Effs x) = prj' (Proxy :: Proxy n) x

type Member :: Effect -> [Effect] -> Constraint
type Member sig sigs = Member' sig sigs (ElemIndex sig sigs)

{-# INLINE inj #-}
inj :: forall sig sigs f a . Member sig sigs => sig f a -> Effs sigs f a
inj = inj' (Proxy :: Proxy (ElemIndex sig sigs))

{-# INLINE prj #-}
prj :: forall sig sigs m a . Member sig sigs => Effs sigs m a -> Maybe (sig m a)
prj = prj' (Proxy :: Proxy (ElemIndex sig sigs))

-- class (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
--   inj :: sig f a -> Effs sigs f a
--   prj :: Effs sigs m a -> Maybe (sig m a)
-- 
-- instance (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
--   {-# INLINE inj #-}
--   inj = inj' (Proxy :: Proxy (ElemIndex sig sigs))
-- 
--   {-# INLINE prj #-}
--   prj = prj' (Proxy :: Proxy (ElemIndex sig sigs))

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

instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  {-# INLINE injs #-}
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

hunion :: forall xs ys f a b
  . ( Append xs (ys :\\ xs)
  ,   Injects (ys :\\ xs) ys )
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs `Union` ys) f a -> b)
hunion xalg yalg = heither @xs @(ys :\\ xs) xalg (yalg . injs)