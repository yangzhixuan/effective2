{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Type
  ( Signature
  , Effect
  , Algebra
  , Effs
  , pattern Eff
  , pattern Effs
  , absurdEffs
  , weakenAlg
  , Injects
  , injs
  , Member (..)
  , inj
  , prj
  , Members
  , hunion
  , heither
  , hinl, hinr
  , houtl, houtr
  , KnownNat
  )
  where

import Data.Kind ( Type )
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts
import Unsafe.Coerce

import Control.Monad.ST
import Data.Array.ST
import Data.Array

type Signature = Type -> Type
type Effect = (Type -> Type) -> (Type -> Type)

type Algebra effs f =
  forall x . Effs effs f x -> f x

-- `Effn n op` places an operation `n` away from the last element of the list.
type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Effn :: HFunctor sig => {-# UNPACK #-} !Int -> !(sig f a) -> Effs sigs f a

pattern Eff :: (HFunctor sig, KnownNat (1 + Length sigs), KnownNat (Length sigs)) => sig f a -> Effs (sig ': sigs) f a
pattern Eff op <- (openEff -> Just op) where
  Eff op = inj op

pattern Effs :: forall sig sigs f a . KnownNat (Length sigs) => Effs sigs f a -> Effs (sig ': sigs) f a
pattern Effs op <- (openEffs -> Just op) where
  Effs op = unsafeCoerce @(Effs sigs f a) @(Effs (sig ': sigs) f a) op

{-# INLINE weakenEffs #-}
weakenEffs :: forall sig sigs f a . Effs sigs f a -> Effs (sig ': sigs) f a
weakenEffs = unsafeCoerce @(Effs sigs f a) @(Effs (sig ': sigs) f a)

{-# INLINE open #-}
open :: forall sig sigs f a . KnownNat (Length sigs) => Effs (sig ': sigs) f a -> Either (Effs sigs f a) (sig f a)
open  eff@(Effn n op)
  | n == fromInteger (fromSNat (natSing @(Length sigs))) = Right (unsafeCoerce @(_ f a) @(sig f a) op)
  | otherwise                                            = Left (unsafeCoerce @(Effs (sig ': sigs) f a) @(Effs sigs f a) eff)

{-# INLINE openEff #-}
openEff :: forall sig sigs f a . Member sig sigs
  => Effs sigs f a -> Maybe (sig f a)
openEff (Effn n op)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(sig f a) op)
  | otherwise = Nothing
  where n' = fromInteger (fromSNat (natSing @(EffIndex sig sigs)))

{-# INLINE openEffs #-}
openEffs :: forall sig sigs f a . KnownNat (Length sigs)
  => Effs (sig ': sigs) f a -> Maybe (Effs sigs f a)
openEffs effn@(Effn n op)
  | n == m    = Nothing
  | otherwise = Just (unsafeCoerce @(Effs (sig ': sigs) f a) @(Effs sigs f a) effn)
  where
    m = fromInteger (fromSNat (natSing @(Length sigs)))

instance Functor f => Functor (Effs sigs f) where
  {-# INLINE fmap #-}
  fmap f (Effn n op) = Effn n (fmap f op)

instance HFunctor (Effs sigs) where
  {-# INLINE hmap #-}
  hmap h (Effn n op) = Effn n (hmap h op)

{-# INLINE absurdEffs #-}
absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}

{-# INLINE heither #-}
heither :: forall xs ys f a b . KnownNat (Length ys)
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs :++ ys) f a -> b)
heither xalg yalg (Effn n op)
  | n < m     = yalg (Effn n op)
  | otherwise = xalg (Effn (n - m) op)
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE hinl #-}
hinl :: forall xs ys f a . KnownNat (Length ys)
  => Effs xs f a -> Effs (xs :++ ys) f a
hinl (Effn n op) = Effn (m + n) op
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE hinr #-}
hinr :: forall xs ys f a . Effs ys f a -> Effs (xs :++ ys) f a
hinr = unsafeCoerce @(Effs ys f a) @(Effs (xs :++ ys) f a)

{-# INLINE houtl #-}
houtl :: forall xs ys f a . KnownNat (Length ys)
  => Effs (xs :++ ys) f a -> Maybe (Effs xs f a)
houtl (Effn n op)
  | n < m     = Nothing
  | otherwise = Just (Effn (n - m) op)
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE houtr #-}
houtr :: forall xs ys f a . KnownNat (Length ys)
  => Effs (xs :++ ys) f a -> Maybe (Effs ys f a)
houtr effn@(Effn n op)
  | n < m     = Just (unsafeCoerce @(Effs (xs :++ ys) f a) @(Effs ys f a) effn)
  | otherwise = Nothing
  where
    m = fromInteger (fromSNat (natSing @(Length ys)))

{-# INLINE weakenAlg #-}
weakenAlg
  :: forall xeffs xyeffs m x . (Injects xeffs xyeffs)
  => (Effs xyeffs m x -> m x)
  -> (Effs xeffs  m x -> m x)
weakenAlg alg = alg . injs

type Member :: Effect -> [Effect] -> Constraint
type Member sig sigs = (KnownNat (EffIndex sig sigs))

type family Members (xeffs :: [Effect]) (xyeffs :: [Effect]) :: Constraint where
  Members '[] xyeffs       = ()
  Members (xeff ': xeffs) xyeffs = (Member xeff xyeffs, Members xeffs xyeffs)


{-# INLINE inj #-}
inj :: forall sig sigs f a . (HFunctor sig, Member sig sigs) => sig f a -> Effs sigs f a
inj = Effn n
  where
    n = fromInteger (fromSNat (natSing @(EffIndex sig sigs)))

{-# INLINE prj #-}
prj :: forall sig sigs f a . (Member sig sigs)
  => Effs sigs f a -> Maybe (sig f a)
prj (Effn n x)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(sig f a) x)
  | otherwise = Nothing
  where
    n' = fromInteger (fromSNat (natSing @(EffIndex sig sigs)))

-- Injects xs ys means that all of xs is in xys
-- Some other effects may be in xys, so xs <= ys
class KnownNat (Length xeffs) => Injects xeffs xyeffs where
  injs :: Effs xeffs f a -> Effs xyeffs f a
  ixs :: Array Int Int

instance (KnownNats (EffIndexes xeffs xyeffs), KnownNat (Length xeffs))
  => Injects xeffs xyeffs where
  {-# INLINE injs #-}
  injs (Effn n op) = Effn (ixs @xeffs @xyeffs ! n) op

  ixs = runSTArray $ do arr <- newArray_ (0, m - 1)
                        natVals (proxy# :: Proxy# (EffIndexes xeffs xyeffs)) arr
                        return arr
    where
      m = fromInteger (natVal' (proxy# :: Proxy# (Length xeffs)))

-- extract the effect from list of xeffs using the natural,
-- and inject it back into yeffs if it is present there
-- injs' :: ElemIndexes xeffs yeffs => Effs xeffs f a -> Effs yeffs f a
-- injs' (Effn n op) = undefined

{-# INLINE hunion #-}
hunion :: forall xeffs yeffs f a b . Injects (yeffs :\\ xeffs) yeffs
  => (Effs xeffs f a -> b) -> (Effs yeffs f a -> b)
  -> (Effs (xeffs `Union` yeffs) f a -> b)
hunion xalg yalg = heither @xeffs @(yeffs :\\ xeffs) xalg (yalg . injs)

type family EffIndex (x :: a) (xs :: [a]) :: Nat where
  EffIndex x (x ': xs) = Length xs
  EffIndex x (_ ': xs) = EffIndex x xs

type family EffIndexes (xs :: [a]) (ys :: [a]) :: [Nat] where
  EffIndexes '[] ys       = '[]
  EffIndexes (x ': xs) ys = EffIndex x ys ': EffIndexes xs ys

class KnownNat (Length ns) => KnownNats (ns :: [Nat]) where
  natVals :: Proxy# ns -> STArray s Int Int -> ST s ()

instance KnownNats '[] where
  natVals _ _ = return ()

instance (KnownNat x, KnownNats xs, KnownNat (Length (x ': xs))) => KnownNats (x ': xs) where
  natVals _ arr = do writeArray arr (fromInteger $ natVal' (proxy# @(Length xs)))
                                    (fromInteger $ natVal' (proxy# @x))
                     natVals (proxy# :: Proxy# xs) arr
