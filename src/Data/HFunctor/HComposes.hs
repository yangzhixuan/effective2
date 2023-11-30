{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Data.HFunctor.HComposes where

import Data.Kind ( Type )
import Data.HFunctor ( HFunctor(..) )
import Data.List.Kind ( type (:++) )
import Control.Monad.Trans.Class ( MonadTrans, lift )

type family HComposes
    (hs :: [(Type -> Type) -> (Type -> Type)])
    (f  :: Type -> Type) :: Type -> Type where
  HComposes '[]       f = f
  HComposes (h ': hs) f = h (HComposes hs f)

type HComps :: [(Type -> Type) -> (Type -> Type)] -> (Type -> Type) -> Type -> Type
data HComps hs f a where
  HNil  :: f a -> HComps '[] f a
  HCons :: (Functor (h (HComps hs f))) => h (HComps hs f) a -> HComps (h ': hs) f a

instance Functor f => Functor (HComps ts f) where
  fmap f (HNil x)  = HNil  (fmap f x)
  fmap f (HCons x) = HCons (fmap f x)

instance Applicative f => Applicative (HComps '[] f) where
  pure x = HNil (pure x)
  HNil mf <*> HNil mx = HNil (mf <*> mx)

instance (Applicative f, Applicative (h (HComps hs f)))
  => Applicative (HComps (h ': hs) f) where
  pure x = HCons (pure x)
  HCons mf <*> HCons mx = HCons (mf <*> mx)

instance Monad m => Monad (HComps '[] m) where
  (>>=) :: Monad m
    => HComps '[] m a -> (a -> HComps '[] m b) -> HComps '[] m b
  HNil mx >>= f = HNil (mx >>= ((\(HNil x) -> x) . f))

instance (Monad m, Monad (t (HComps ts m)) ) => Monad (HComps (t ': ts) m) where
  (>>=) :: HComps (t : ts) m a -> (a -> HComps (t : ts) m b) -> HComps (t : ts) m b
  HCons mx >>= f = HCons (mx >>= ((\(HCons x) -> x) . f))

instance MonadTrans (HComps '[]) where
  lift = HNil

instance (MonadTrans t, MonadTrans (HComps ts))
  => MonadTrans (HComps (t ': ts)) where
  lift x = HCons (lift (lift x))

hdecomps :: (HFunctor h, Functor f) => HComps '[h] f x -> h f x
hdecomps (HCons x) = hmap (\(HNil y) -> y) x

hcomps :: (HFunctor h, Functor f) => h f x -> HComps '[h] f x
hcomps = HCons . hmap HNil

class HRecompose hs f where
  hrecompose :: HComps hs f a -> HComposes hs f a
  hdecompose :: HComposes hs f a -> HComps hs f a

instance HRecompose '[] f where
  hrecompose :: HComps '[] f a -> HComposes '[] f a
  hrecompose (HNil x)  = x

  hdecompose :: HComposes '[] f a -> HComps '[] f a
  hdecompose = HNil

instance (Functor f, Functor (HComposes hs f), HRecompose hs f, HFunctor h)
  => HRecompose (h ': hs) f where
  hrecompose :: (Functor f, Functor (HComposes hs f), HRecompose hs f, HFunctor h)
    => HComps (h ': hs) f a -> HComposes (h ': hs) f a
  hrecompose (HCons x) = hmap hrecompose x

  hdecompose :: (Functor f, Functor (HComposes hs f), HRecompose hs f)
    => HComposes (h ': hs) f a -> HComps (h ': hs) f a
  hdecompose x = HCons (hmap hdecompose x)

class (forall f . Functor f => Functor (HComps hs f)) => HExpose hs where
  hexpose   :: Functor f => HComps (hs :++ ks) f a -> HComps hs (HComps ks f) a
  hunexpose :: Functor f => HComps hs (HComps ks f) a -> HComps (hs :++ ks) f a

instance HExpose '[] where
  hexpose :: Functor f => HComps ks f a -> HComps '[] (HComps ks f) a
  hexpose (HNil x)  = HNil (HNil x)
  hexpose (HCons x) = HNil (HCons x)

  hunexpose :: HComps '[] (HComps ks f) a -> HComps ('[] :++ ks) f a
  hunexpose (HNil x)  = x

instance (HExpose hs , HFunctor h) => HExpose (h ': hs) where
  hexpose :: Functor f => HComps ((h ': hs) :++ ks) f a -> HComps (h ': hs) (HComps ks f) a
  hexpose   (HCons x) = HCons (hmap hexpose x)

  hunexpose :: Functor f => HComps (h ': hs) (HComps ks f) a -> HComps ((h ': hs) :++ ks) f a
  hunexpose (HCons x) = HCons (hmap hunexpose x)

