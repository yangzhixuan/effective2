{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Functor.Composes (RSplit(..), RComposes(..), RComps(..), Functors(..)) where

import Data.Kind ( Type )

import Data.List.Kind ( type (:++) )

class Functors fs where
instance Functors '[]
instance (Functors fs, Functor f) => Functors (f ': fs)

----------------------------------------------
-- Composes is a non-injective type family because it has:
-- * a bare variable in the first clause:
--     Composes '[] a = a
--   the variable `a` on the RHS is not allowed to be bare
-- * There is an overlap on the RHS between `a` and `f x` for any `x`
--
type family Composes (fs :: [Type -> Type]) (a :: Type) :: Type where
  Composes '[]       a = a
  Composes (f ': fs) a = f (Composes fs a)

newtype Comps fs a = Comps { unComps :: Composes fs a }

instance Functor (Comps '[]) where
  fmap f (Comps x) = Comps (f x)

instance forall f fs . (Functor f, Functor (Comps fs)) => Functor (Comps (f ': fs)) where
  fmap f (Comps x) = Comps (fmap (unComps . fmap @(Comps fs) f . Comps) x)

class Expose fs where
  expose :: Comps (fs :++ gs) a -> Comps fs (Comps gs a)
  unexpose :: Comps fs (Comps gs a) -> Comps (fs :++ gs) a

instance Expose '[] where
  expose :: Comps ('[] :++ gs) a -> Comps '[] (Comps gs a)
  expose (Comps x) = Comps (Comps x)

  unexpose :: Comps '[] (Comps gs a) -> Comps gs a
  unexpose (Comps x)  = x

instance (Expose fs, Functor f) => Expose (f : fs) where
  expose :: forall gs a . Comps ((f ': fs) :++ gs) a -> Comps (f ': fs) (Comps gs a)
  expose (Comps x) = Comps (fmap (unComps . expose @fs @gs @a . Comps) x)

  unexpose :: forall gs a . Comps (f ': fs) (Comps gs a) -> Comps ((f ': fs) :++ gs) a
  unexpose (Comps x) = Comps (fmap (unComps . unexpose @fs @gs @a . Comps) x)

-- reverse composition
type family RComposes (fs :: [Type -> Type]) (a :: Type) :: Type where
  RComposes '[]       a = a
  RComposes (f ': fs) a = (RComposes fs (f a))

type RComps :: [Type -> Type] -> Type -> Type
newtype RComps fs a = RComps { unRComps :: RComposes fs a }

instance Functor (RComps '[]) where
  {-# INLINE fmap #-}
  fmap f (RComps x) = RComps (f x)

instance forall f fs . (Functor f, Functor (RComps fs)) => Functor (RComps (f ': fs)) where
  {-# INLINE fmap #-}
  fmap :: forall a b . (Functor f, Functor (RComps fs)) => (a -> b) -> RComps (f : fs) a -> RComps (f : fs) b
  fmap f (RComps x) = RComps ((unRComps . fmap @(RComps fs) (fmap @f f) . RComps) x)

-- The proof is the same as the reverse split law:
--   reverse (xs ++ ys) = reverse ys ++ reverse xs
class RSplit fs where
  rsplit   :: Functor (RComps gs) => RComps (fs :++ gs) a -> RComps gs (RComps fs a)
  unrsplit :: Functor (RComps gs) => RComps gs (RComps fs a) -> RComps (fs :++ gs) a

instance RSplit '[] where
  {-# INLINE rsplit #-}
  rsplit   :: forall gs a . Functor (RComps gs) => RComps ('[] :++ gs) a -> RComps gs (RComps '[] a)
  rsplit (RComps x) = (fmap RComps . RComps) x

  {-# INLINE unrsplit #-}
  unrsplit :: Functor (RComps gs) => RComps gs (RComps '[] a) -> RComps gs a
  unrsplit x = (fmap unRComps) x

instance RSplit fs => RSplit (f ': fs) where
  {-# INLINE rsplit #-}
  rsplit   :: forall gs a . Functor (RComps gs) => RComps ((f ': fs) :++ gs) a -> RComps gs (RComps (f ': fs) a)
  rsplit (RComps x) = (fmap (RComps @(f ': fs) . unRComps @fs) . rsplit @fs @gs . RComps @(fs :++ gs) @(f a)) x

  {-# INLINE unrsplit #-}
  unrsplit :: forall gs a . Functor (RComps gs) => RComps gs (RComps (f ': fs) a) -> RComps ((f ': fs) :++ gs) a
  unrsplit x = ((RComps. unRComps) . unrsplit @fs @gs @(f a) . (fmap (RComps . unRComps))) x