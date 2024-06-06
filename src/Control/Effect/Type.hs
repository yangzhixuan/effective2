{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Type where

import Data.Kind ( Type, Constraint )
import Data.HFunctor
import Data.Functor.Composes
import Control.Monad.Trans.Class
import Data.List.Kind
import Data.Nat

type Signature = Type -> Type
type Effect = (Type -> Type) -> (Type -> Type)

type Algebra effs f =
   forall x . Effs effs f x -> f x

type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Eff  :: HFunctor sig => sig f a -> Effs (sig ': sigs) f a
  Effs :: Effs sigs f a -> Effs (sig ': sigs) f a

type Handler
  :: [Effect]                          -- effs  : input effects
  -> [Effect]                          -- oeffs : output effects
  -> [Type -> Type]                    -- f     : carrier type
  -> Type
data Handler effs oeffs fs
  =  forall t . (MonadTrans t)
  => Handler (Handler' effs oeffs t fs)

type Handler'
  :: [Effect]                             -- effs  : input effects
  -> [Effect]                             -- oeffs : output effects
  -> ((Type -> Type) -> (Type -> Type))   -- t     : monad transformer
  -> [Type -> Type]                       -- f     : carrier type
  -> Type
data Handler' effs oeffs t fs =
  Handler'
  { run  :: forall m . Monad m
         => Algebra oeffs m
         -> (forall x . t m x -> m (RComps fs x))

  , malg :: forall m . Monad m
         => Algebra oeffs m -> Algebra effs (t m)
  }

{-
The original version of Handler included a forwarder:
```
   mfwd :: forall m sig . Monad m
         => (forall x . Effs sig m x -> m x)
         -> (forall x . Effs sig (t m) x -> t m x)
```
This was replaced by the `Forward` class, which works with families,
since it is too onerous forward every form of signature.

An alternative design would be for the forwarding function to be
provided when the handler is constructed, by the `Forward` class.
However, this means that the family of values that can be
forwarded is then exposed at the type level of the handler type:
```
  data Handler' effs oeffs t fs feffs
```
where `feffs` are the effects that can be forwarded, and then we would need
constraints such as `Forward feffs t` to be in place. The advantage
is that custom effects can forward more flexibly, but at the cost
of added complexity in the signature.

That complexity could be hidden by another datatype, much
in the same way as `Handler` obscures the underlying `t` type.
-}

type SNat :: Nat -> Type
data SNat n = SNat
-- injecting/projecting at a specified position SNat n

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