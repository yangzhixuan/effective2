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

{-
A list of higher-order functors can be composed to make a higher-order
functor, and this idea is implemented in the `HComps` type below.
-}
type HComps :: [(Type -> Type) -> (Type -> Type)] -> (Type -> Type) -> Type -> Type
newtype HComps hs f a = HComps { unHComps :: HComposes hs f a }

--   HNil  :: f a -> HComps '[] f a
--   HCons :: h (HComps hs f) a -> HComps (h ': hs) f a
--   HCons :: Functor (h (HComps hs f)) => h (HComps hs f) a -> HComps (h ': hs) f a

{-# INLINE unHNil #-}
unHNil :: HComps '[] f a -> f a
unHNil = unHComps

{-# INLINE unHCons #-}
unHCons :: (HFunctor h, Functor f, Functor (HComposes hs f), Functor (HComps hs f)) => HComps (h ': hs) f a -> h (HComps hs f) a
unHCons (HComps x) = hmap HComps x

{-# INLINE hdecomps #-}
hdecomps :: HComps '[h] f a -> h f a
hdecomps (HComps x) = x

{-# INLINE hcomps #-}
hcomps :: h f a -> HComps '[h] f a
hcomps = HComps
{-
Without the `Functor (h (HComps hs f))` constraint, the following
functor instance would not work as is:
-}
instance Functor f => Functor (HComps '[] f) where
  {-# INLINE fmap #-}
  fmap f (HComps x)  = HComps (fmap f x)

instance (Functor f, Functor (HComps ts f), Functor (t (HComposes ts f))) => Functor (HComps (t ': ts) f) where
  {-# INLINE fmap #-}
  fmap f (HComps x)  = HComps (fmap f x)

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
    pure x = HComps (pure x)
    {-# INLINE (<*>) #-}
    HComps mf <*> HComps mx = HComps (mf <*> mx)

instance (Applicative f, Applicative (HComps hs f) , Applicative (h (HComposes hs f))) =>
  Applicative (HComps (h ': hs) f) where
    {-# INLINE pure #-}
    pure x = HComps (pure x)
    {-# INLINE (<*>) #-}
    HComps mf <*> HComps mx = HComps (mf <*> mx)

instance Monad m =>
  Monad (HComps '[] m) where
    {-# INLINE (>>=) #-}
    (>>=) :: Monad m => HComps '[] m a -> (a -> HComps '[] m b) -> HComps '[] m b
    HComps mx >>= f = HComps (mx >>= ((\(HComps x) -> x) . f))

instance (Monad m, Monad (HComps ts m), MonadTrans t) =>
  Monad (HComps (t ': ts) m) where
    {-# INLINE (>>=) #-}
    (>>=) :: HComps (t : ts) m a -> (a -> HComps (t : ts) m b) -> HComps (t : ts) m b
    HComps mx >>= f = undefined -- HComps (mx >>= ((\(HComps x) -> x) . f))

instance HFunctor (HComps '[]) where
  {-# INLINE hmap #-}
  hmap h (HComps x) = HComps (h x)
instance (HFunctor h, HFunctor (HComps hs)) =>
  HFunctor (HComps (h ': hs)) where
    {-# INLINE hmap #-}
    hmap :: forall f g a.  (forall x. f x -> g x) -> HComps (h : hs) f a -> HComps (h : hs) g a
    hmap h (HComps x) = HComps (hmap (unHComps . hmap @(HComps hs) @f @g  h . HComps) x)

instance MonadTrans (HComps '[]) where
  {-# INLINE lift #-}
  lift = HComps
instance (MonadTrans t, MonadTrans (HComps ts))
  => MonadTrans (HComps (t ': ts)) where
  {-# INLINE lift #-}
  lift x = undefined -- HComps (lift (lift x))

class HRecompose hs f where
  hrecompose :: HComps hs f a -> HComposes hs f a
  hdecompose :: HComposes hs f a -> HComps hs f a

instance HRecompose '[] f where
  {-# INLINE hrecompose #-}
  hrecompose :: HComps '[] f a -> HComposes '[] f a
  hrecompose (HComps x)  = x

  {-# INLINE hdecompose #-}
  hdecompose :: HComposes '[] f a -> HComps '[] f a
  hdecompose = HComps

instance (Functor f, Functor (HComposes hs f), Functor (HComps hs f), HRecompose hs f, HFunctor h)
  => HRecompose (h ': hs) f where
  {-# INLINE hrecompose #-}
  hrecompose :: HComps (h ': hs) f a -> HComposes (h ': hs) f a
  hrecompose (HComps x) = undefined -- hmap (hrecompose @hs) x

  {-# INLINE hdecompose #-}
  hdecompose :: HComposes (h ': hs) f a -> HComps (h ': hs) f a
  hdecompose x = undefined -- HComps (hmap hdecompose x)

class HExpose hs where
  hexpose   :: Functor f => HComps (hs :++ ks) f a -> HComps hs (HComps ks f) a
  hunexpose :: Functor f => HComps hs (HComps ks f) a -> HComps (hs :++ ks) f a

instance HExpose '[] where
  {-# INLINE hexpose #-}
  hexpose :: Functor f => HComps ks f a -> HComps '[] (HComps ks f) a
  hexpose (HComps x)  = HComps (HComps x)

  {-# INLINE hunexpose #-}
  hunexpose :: HComps '[] (HComps ks f) a -> HComps ('[] :++ ks) f a
  hunexpose (HComps x)  = x

instance (HExpose hs , HFunctor h, (forall f ks . Functor f => Functor (HComps ks f))) => HExpose (h ': hs) where
  {-# INLINE hexpose #-}
  hexpose   (HComps x) = undefined -- HComps (hmap hexpose x)

  {-# INLINE hunexpose #-}
  hunexpose (HComps x) = undefined -- HComps (hmap hunexpose x)
class HExposes hs ks where
  hexposes   :: HComps (hs :++ ks) f a -> HComps hs (HComps ks f) a
  hunexposes :: HComps hs (HComps ks f) a -> HComps (hs :++ ks) f a

instance HExposes '[] ks where
  {-# INLINE hexposes #-}
  hexposes :: HComps ks f a -> HComps '[] (HComps ks f) a
  hexposes (HComps x)  = HComps (HComps x)

  {-# INLINE hunexposes #-}
  hunexposes :: HComps '[] (HComps ks f) a -> HComps ('[] :++ ks) f a
  hunexposes (HComps x)  = x

instance (HExposes hs ks, HFunctor h, (forall f ks . Functor (HComps ks f))) => HExposes (h ': hs) ks where
  {-# INLINE hexposes #-}
  hexposes   (HComps x) = undefined -- HComps (hmap hexposes x)

  {-# INLINE hunexposes #-}
  hunexposes (HComps x) = undefined -- HComps (hmap hunexposes x)



