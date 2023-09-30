{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Functor.Composes where

import Data.Kind ( Type )

import Data.List.TypeLevel ( type (:++) )

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

comps :: Functor f => f x -> Comps '[f] x
comps = CCons . fmap CNil

class Recompose fs where
  recompose :: Comps fs x -> Composes fs x
  decompose :: Composes fs x -> Comps fs x

instance Recompose '[] where
  recompose (CNil x) = x
  decompose = CNil

instance (Recompose fs, Functor f) => Recompose (f ': fs) where
  recompose :: (Recompose fs, Functor f) => Comps (f : fs) x -> Composes (f : fs) x
  recompose (CCons x) = fmap recompose x
  
  decompose :: (Recompose fs, Functor f) => Composes (f : fs) x -> Comps (f : fs) x
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
  expose (CCons x) = CCons (fmap expose x)

  unexpose :: Comps (f ': fs) (Comps gs a) -> Comps ((f ': fs) :++ gs) a
  unexpose (CCons x) = CCons (fmap unexpose x)

