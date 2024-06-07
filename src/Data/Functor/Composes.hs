{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Functor.Composes where

import Data.Kind ( Type )

import Data.List.Kind ( type (:++) )

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

type Comps :: [Type -> Type] -> Type -> Type
data Comps fs a where
  CNil  :: a -> Comps '[] a
  CCons :: f (Comps fs a) -> Comps (f ': fs) a

instance Functor (Comps '[]) where
  fmap f (CNil x) = CNil (f x)

instance (Functor f, Functor (Comps fs)) => Functor (Comps (f ': fs)) where
  fmap f (CCons x) = CCons (fmap (fmap f) x)

decomps :: Functor f => Comps '[f] a -> f a
decomps (CCons x) = fmap (\(CNil y) -> y) x

comps :: Functor f => f a -> Comps '[f] a
comps = CCons . fmap CNil

class Recompose fs where
  recompose :: Comps fs a -> Composes fs a
  decompose :: Composes fs a -> Comps fs a

instance Recompose '[] where
  recompose (CNil x) = x
  decompose = CNil

instance (Recompose fs, Functor f) => Recompose (f ': fs) where
  recompose :: (Recompose fs, Functor f) => Comps (f : fs) a -> Composes (f : fs) a
  recompose (CCons x) = fmap recompose x

  decompose :: (Recompose fs, Functor f) => Composes (f : fs) a -> Comps (f : fs) a
  decompose x = CCons (fmap decompose x)


class Expose fs where
  expose :: Comps (fs :++ gs) a -> Comps fs (Comps gs a)
  unexpose :: Comps fs (Comps gs a) -> Comps (fs :++ gs) a

instance Expose '[] where
  expose :: Comps ('[] :++ gs) a -> Comps '[] (Comps gs a)
  expose (CNil x)  = CNil (CNil x)
  expose (CCons x) = CNil (CCons x)

  unexpose :: Comps '[] (Comps gs a) -> Comps gs a
  unexpose (CNil x)  = x

instance (Expose fs, Functor f) => Expose (f : fs) where
  expose (CCons x) = (CCons . fmap expose) x

  unexpose :: Comps (f ': fs) (Comps gs a) -> Comps ((f ': fs) :++ gs) a
  unexpose (CCons x) = CCons (fmap unexpose x)

-- This version is for convienience, when having the extra argument `gs` helps
-- with inference.
class Exposes fs gs where
  exposes :: Comps (fs :++ gs) a -> Comps fs (Comps gs a)
  unexposes :: Comps fs (Comps gs a) -> Comps (fs :++ gs) a

instance Exposes '[] gs where
  exposes :: Comps ('[] :++ gs) a -> Comps '[] (Comps gs a)
  exposes (CNil x)  = CNil (CNil x)
  exposes (CCons x) = CNil (CCons x)

  unexposes :: Comps '[] (Comps gs a) -> Comps gs a
  unexposes (CNil x)  = x

instance (Exposes fs gs, Functor f) => Exposes (f : fs) gs where
  exposes (CCons x) = CCons (fmap exposes x)

  unexposes :: Comps (f ': fs) (Comps gs a) -> Comps ((f ': fs) :++ gs) a
  unexposes (CCons x) = CCons (fmap unexposes x)

-- reverse composition
type family RComposes (fs :: [Type -> Type]) (a :: Type) :: Type where
  RComposes '[]       a = a
  RComposes (f ': fs) a = (RComposes fs (f a))

type RComps :: [Type -> Type] -> Type -> Type
data RComps fs a where
  RCNil  :: a -> RComps '[] a
  RCCons :: RComps fs (f a) -> RComps (f ': fs) a

unrcnil :: RComps '[] a -> a
unrcnil (RCNil x) = x

unrccons :: RComps (f ': fs) a -> RComps fs (f a)
unrccons (RCCons x) = x

instance Functor (RComps '[]) where
  fmap f (RCNil x) = RCNil (f x)

instance (Functor f, Functor (RComps fs)) => Functor (RComps (f ': fs)) where
  fmap :: (Functor f, Functor (RComps fs)) => (a -> b) -> RComps (f : fs) a -> RComps (f : fs) b
  fmap f (RCCons x) = RCCons (fmap (fmap f) x)

class Rercompose fs where
  rercompose :: RComps fs a -> RComposes fs a
  dercompose :: RComposes fs a -> RComps fs a

instance Rercompose '[] where
  rercompose (RCNil x) = x
  dercompose = RCNil

instance (Rercompose fs, Functor f) => Rercompose (f ': fs) where
  rercompose :: (Rercompose fs, Functor f) => RComps (f : fs) a -> RComposes (f : fs) a
  rercompose (RCCons x) = rercompose x

  dercompose :: (Rercompose fs, Functor f) => RComposes (f : fs) a -> RComps (f : fs) a
  -- dercompose x = RCCons (fmap dercompose x)
  dercompose x = RCCons (dercompose x)

rcomps :: Functor f => f a -> RComps '[f] a
rcomps = RCCons . RCNil

-- The proof is the same as the reverse split law:
--   reverse (xs ++ ys) = reverse ys ++ reverse xs
class RSplit fs where
  rsplit   :: Functor (RComps gs) => RComps (fs :++ gs) a -> RComps gs (RComps fs a)
  unrsplit :: Functor (RComps gs) => RComps gs (RComps fs a) -> RComps (fs :++ gs) a

instance RSplit '[] where
  rsplit   :: Functor (RComps gs) => RComps ('[] :++ gs) a -> RComps gs (RComps '[] a)
  rsplit (RCNil x) = RCNil (RCNil x)
  rsplit (RCCons x) = (fmap RCNil . RCCons) x

  unrsplit :: Functor (RComps gs) => RComps gs (RComps '[] a) -> RComps gs a
  unrsplit x = (fmap unrcnil) x

instance RSplit fs => RSplit (f ': fs) where
  rsplit   :: Functor (RComps gs) => RComps ((f ': fs) :++ gs) a -> RComps gs (RComps (f ': fs) a)
  rsplit (RCCons x) = (fmap RCCons . rsplit) x

  unrsplit :: Functor (RComps gs) => RComps gs (RComps (f ': fs) a) -> RComps ((f ': fs) :++ gs) a
  unrsplit x = (RCCons . unrsplit . fmap unrccons) x