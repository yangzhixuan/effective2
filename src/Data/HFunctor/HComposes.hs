{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Monad.Trans.Composes where

import Data.Kind ( Type )
import Data.HFunctor ( HFunctor(..) )
import Data.List.Kind ( type (:++) )
import Control.Monad.Trans.Class ( MonadTrans, lift )

type family ComposeTs
    (hs :: [(Type -> Type) -> (Type -> Type)])
    (f  :: Type -> Type) :: Type -> Type where
  ComposeTs '[]       f = f
  ComposeTs (h ': hs) f = h (ComposeTs hs f)

{-
A list of higher-order functors can be composed to make a higher-order
functor, and this idea is implemented in the `HComps` type below.
-}
type HComps :: [(Type -> Type) -> (Type -> Type)] -> (Type -> Type) -> Type -> Type
data HComps hs f a where
  HNil  :: f a -> HComps '[] f a
  -- HCons :: h (HComps hs f) a -> HComps (h ': hs) f a
  HCons :: Functor (h (HComps hs f)) => h (HComps hs f) a -> HComps (h ': hs) f a

{-# INLINE unHNil #-}
unHNil  :: HComps '[] f a -> f a
unHNil (HNil x) = x

{-# INLINE unHCons #-}
unHCons :: HComps (h ': hs) f a -> h (HComps hs f) a
unHCons (HCons x) = x

{-# INLINE hdecomps #-}
hdecomps :: (HFunctor h, Functor f) => HComps '[h] f a -> h f a
hdecomps (HCons x) = hmap unHNil x

{-# INLINE hcomps #-}
hcomps :: (HFunctor h, Functor f) => h f a -> HComps '[h] f a
hcomps = HCons . hmap HNil
{-
Without the `Functor (h (HComps hs f))` constraint, the following
functor instance would not work as is:
-}
instance Functor f => Functor (HComps ts f) where
  {-# INLINE fmap #-}
  fmap :: Functor f => (a -> b) -> HComps ts f a -> HComps ts f b
  fmap f (HNil x)  = HNil  (fmap f x)
  fmap f (HCons x) = HCons (fmap f x)

{-
The `Functor` instance did not require the type level pattern matching
for its instance definition, but unfortunately this is where the luck ends.
The instance for `Applicative` is interesting because the defintion of `pure` will
differ depending on whether the result is `HComps' '[] f a` or
`HComps' (t ': ts) f a`.

No amount of information from the constructors can help here, since it
is not clear which constructor is even required! `Applicative` is
not the only instance that has this problem:
a similar issue occurs with the `lift :: m x -> HComps ts m x` function,
again, where a `HComps ts m x` must be *produced*.

Thankfully, there is a solution. Multiple instances can be given, one
for the `'[]` case, and another for the `t ': ts` case. Each
instance can be provided with suitable constraints such that none
need to be present in the GADT.
-}

-- instance Functor f =>
--   Functor (HComps '[] f) where
--     fmap f (HNil x) = HNil (fmap f x)
-- instance (Functor (h (HComps hs f))) =>
--   Functor (HComps (h ': hs) f) where
--     fmap f (HCons x) = HCons . fmap f $ x

{-
An alternative set of constraints for the `h ': hs` case is:
```
instance (Functor f, HFunctor h, Functor (HComps hs f)) =>
  Functor (HComps (h ': hs) f) where
```
From these constraints, we derive that `Functor (h (HComps hs f))`,
which is all that is required for the `fmap` in the definition.

Using this idea, the remaining instances are fairly routine to implement.
-}
instance Applicative f =>
  Applicative (HComps '[] f) where
    {-# INLINE pure #-}
    pure x = HNil (pure x)
    {-# INLINE (<*>) #-}
    HNil mf <*> HNil mx = HNil (mf <*> mx)
instance (Applicative f, Applicative (h (HComps hs f))) =>
  Applicative (HComps (h ': hs) f) where
    {-# INLINE pure #-}
    pure x = HCons (pure x)
    {-# INLINE (<*>) #-}
    HCons mf <*> HCons mx = HCons (mf <*> mx)

instance Monad m =>
  Monad (HComps '[] m) where
    {-# INLINE (>>=) #-}
    (>>=) :: Monad m => HComps '[] m a -> (a -> HComps '[] m b) -> HComps '[] m b
    HNil mx >>= f = HNil (mx >>= ((\(HNil x) -> x) . f))
instance (Monad m, Monad (t (HComps ts m))) =>
  Monad (HComps (t ': ts) m) where
    {-# INLINE (>>=) #-}
    (>>=) :: HComps (t : ts) m a -> (a -> HComps (t : ts) m b) -> HComps (t : ts) m b
    HCons mx >>= f = HCons (mx >>= ((\(HCons x) -> x) . f))

instance HFunctor (HComps '[]) where
  {-# INLINE hmap #-}
  hmap h (HNil x) = HNil (h x)
instance (HFunctor h, HFunctor (HComps hs)) =>
  HFunctor (HComps (h ': hs)) where
    {-# INLINE hmap #-}
    hmap h (HCons x) = HCons (hmap (hmap h) x)

instance MonadTrans (HComps '[]) where
  {-# INLINE lift #-}
  lift = HNil
instance (MonadTrans t, MonadTrans (HComps ts))
  => MonadTrans (HComps (t ': ts)) where
  {-# INLINE lift #-}
  lift x = HCons (lift (lift x))

class HRecompose hs f where
  hrecompose :: HComps hs f a -> ComposeTs hs f a
  hdecompose :: ComposeTs hs f a -> HComps hs f a

instance HRecompose '[] f where
  {-# INLINE hrecompose #-}
  hrecompose :: HComps '[] f a -> ComposeTs '[] f a
  hrecompose (HNil x)  = x

  {-# INLINE hdecompose #-}
  hdecompose :: ComposeTs '[] f a -> HComps '[] f a
  hdecompose = HNil

instance (Functor f, Functor (ComposeTs hs f), Functor (HComps hs f), HRecompose hs f, HFunctor h)
  => HRecompose (h ': hs) f where
  {-# INLINE hrecompose #-}
  hrecompose :: HComps (h ': hs) f a -> ComposeTs (h ': hs) f a
  hrecompose (HCons x) = hmap hrecompose x

  {-# INLINE hdecompose #-}
  hdecompose :: ComposeTs (h ': hs) f a -> HComps (h ': hs) f a
  hdecompose x = HCons (hmap hdecompose x)

class HExpose hs where
  hexpose   :: Functor f => HComps (hs :++ ks) f a -> HComps hs (HComps ks f) a
  hunexpose :: Functor f => HComps hs (HComps ks f) a -> HComps (hs :++ ks) f a

instance HExpose '[] where
  {-# INLINE hexpose #-}
  hexpose :: Functor f => HComps ks f a -> HComps '[] (HComps ks f) a
  hexpose (HNil x)  = HNil (HNil x)
  hexpose (HCons x) = HNil (HCons x)

  {-# INLINE hunexpose #-}
  hunexpose :: HComps '[] (HComps ks f) a -> HComps ('[] :++ ks) f a
  hunexpose (HNil x)  = x

instance (HExpose hs , HFunctor h, (forall f ks . Functor f => Functor (HComps ks f))) => HExpose (h ': hs) where
  {-# INLINE hexpose #-}
  hexpose   (HCons x) = HCons (hmap hexpose x)

  {-# INLINE hunexpose #-}
  hunexpose (HCons x) = HCons (hmap hunexpose x)
class HExposes hs ks where
  hexposes   :: HComps (hs :++ ks) f a -> HComps hs (HComps ks f) a
  hunexposes :: HComps hs (HComps ks f) a -> HComps (hs :++ ks) f a

instance HExposes '[] ks where
  {-# INLINE hexposes #-}
  hexposes :: HComps ks f a -> HComps '[] (HComps ks f) a
  hexposes (HNil x)  = HNil (HNil x)
  hexposes (HCons x) = HNil (HCons x)

  {-# INLINE hunexposes #-}
  hunexposes :: HComps '[] (HComps ks f) a -> HComps ('[] :++ ks) f a
  hunexposes (HNil x)  = x

instance (HExposes hs ks, HFunctor h, (forall f ks . Functor (HComps ks f))) => HExposes (h ': hs) ks where
  {-# INLINE hexposes #-}
  hexposes   (HCons x) = HCons (hmap hexposes x)

  {-# INLINE hunexposes #-}
  hunexposes (HCons x) = HCons (hmap hunexposes x)



