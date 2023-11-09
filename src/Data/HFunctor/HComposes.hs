{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}


module Data.HFunctor.HComposes where

import Data.Kind ( Type )
import Data.HFunctor ( HFunctor(..) )
import Data.List.Kind ( type (:++) )
import Control.Monad.Trans.Class ( MonadTrans )

import Data.SOP.Constraint ( All )

type family HComposes
    (hs :: [(Type -> Type) -> (Type -> Type)])
    (f  :: Type -> Type) :: Type -> Type where
  HComposes '[]       f = f
  HComposes (h ': hs) f = h (HComposes hs f)

type HComps :: [(Type -> Type) -> (Type -> Type)] -> (Type -> Type) -> Type -> Type
data HComps hs f a where
  HNil  :: f a -> HComps '[] f a
  HCons :: (Functor (h (HComps hs f))) => h (HComps hs f) a -> HComps (h ': hs) f a

instance Functor f => Functor (HComps t2 f) where
  fmap f (HNil x)  = HNil  (fmap f x)
  fmap f (HCons x) = HCons (fmap f x)

instance Monad m => Applicative (HComps '[] m) where
  pure x = HNil (pure x)
  HNil mf <*> HNil mx = HNil (mf <*> mx)

instance (MonadTrans t, Monad m, Monad (HComps ts m)) => Applicative (HComps (t ': ts) m) where
  pure x = HCons (pure x)
  HCons mf <*> HCons mx = HCons (mf <*> mx)

instance Monad m => Monad (HComps '[] m) where
  (>>=) :: Monad m 
    => HComps '[] m a -> (a -> HComps '[] m b) -> HComps '[] m b
  HNil mx >>= f = HNil (mx >>= ((\(HNil x) -> x) . f))

instance (MonadTrans t, Monad m, Monad (HComps ts m)) => Monad (HComps (t ': ts) m) where
  (>>=) :: (MonadTrans t, Monad m, Monad (HComps ts m))
    => HComps (t : ts) m a -> (a -> HComps (t : ts) m b) -> HComps (t : ts) m b
  HCons mx >>= f = HCons (mx >>= ((\(HCons x) -> x) . f))
 
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

instance (All MonadTrans ts, Functor m, Functor (HComposes ts m), HRecompose ts m, HFunctor t) 
  => HRecompose (t ': ts) m where
  hrecompose :: (All MonadTrans ts, Functor m, Functor (HComposes ts m), HRecompose ts m, HFunctor t) 
    => HComps (t : ts) m a -> HComposes (t : ts) m a
  hrecompose (HCons x) = hmap hrecompose x

  hdecompose :: (All MonadTrans ts, Functor m, Functor (HComposes ts m), HRecompose ts m, HFunctor t)
    => HComposes (t : ts) m a -> HComps (t : ts) m a
  hdecompose x = HCons (hmap hdecompose x)

class HExpose hs where
  hexpose :: Monad m => HComps (hs :++ ks) m a -> HComps hs (HComps ks m) a
  hunexpose :: Monad m => HComps hs (HComps ks m) a -> HComps (hs :++ ks) m a

instance HExpose '[] where
  hexpose :: Monad m => HComps ks m a -> HComps '[] (HComps ks m) a
  hexpose (HNil x)  = HNil (HNil x)
  hexpose (HCons x) = HNil (HCons x)

  hunexpose :: Monad m => HComps '[] (HComps ks m) a -> HComps ('[] :++ ks) m a
  hunexpose (HNil x)  = x
 
instance (HExpose hs , HFunctor h) => HExpose (h ': hs) where
  hexpose (HCons x) = HCons (hmap hexpose x)
  hunexpose (HCons x) = HCons (hmap hunexpose x)

