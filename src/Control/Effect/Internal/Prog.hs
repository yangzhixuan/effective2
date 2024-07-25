{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Internal.Prog where
import Control.Effect.Internal.Effs

import Data.HFunctor
import Control.Monad

---------------------------------------
-- | `Progs sig a` desribes a family of
type Progs sig a = forall sig' . Members sig sig' => Prog sig' a
data Prog (sigs :: [Effect]) a where
  Return :: a -> Prog sigs a
  -- Call'   :: (Effs sigs) (Prog sigs) (Prog sigs a) -> Prog sigs a
  -- Call' x ~= Call x id return

  Call  :: forall sigs a f x
        .  Functor f
        => (Effs sigs) f x
        -> (forall x . f x -> Prog sigs x)
        -> (x -> Prog sigs a)
        -> Prog sigs a

instance Functor (Prog sigs) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap f (Return x)     = Return (f x)
  fmap f (Call op hk k) = Call op hk (fmap f . k)

instance Applicative (Prog effs) where
  {-# INLINE pure #-}
  pure :: a -> Prog effs a
  pure  = Return

  {-# INLINE (<*>) #-}
  (<*>) :: Prog effs (a -> b) -> Prog effs a -> Prog effs b
  Return f        <*> p = fmap f p
  Call opf hkf kf <*> q = Call opf hkf ((<*> q) . kf)

  {-# INLINE (*>) #-}
  (*>) :: Prog effs a -> Prog effs b -> Prog effs b
  (*>) = liftA2 (const id)

  {-# INLINE (<*) #-}
  (<*) :: Prog effs a -> Prog effs b -> Prog effs a
  (<*) = liftA2 const

  {-# INLINE liftA2 #-}
  liftA2 :: (a -> b -> c) -> Prog effs a -> Prog effs b -> Prog effs c
  liftA2 f (Return x) q        = fmap (f x) q
  liftA2 f (Call opx hkx kx) q = Call opx hkx ((flip (liftA2 f) q) . kx)

instance Monad (Prog effs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  Return x      >>= f = f x
  Call op hk k  >>= f = Call op hk (k >=> f)

weakenProg :: forall effs effs' a
  .  Injects effs effs'
  => Prog effs a -> Prog effs' a
weakenProg (Return x) = Return x
weakenProg (Call op hk k)   =
    Call (injs op) (weakenProg @effs @effs' . hk) (weakenProg @effs @effs' . k)


-- Universal property from initial monad `Prog sig a` equipped with
-- `sig m -> m`
eval :: forall effs m a . Monad m
  => Algebra effs m
  -> Prog effs a -> m a
eval halg (Return x) = return x
eval halg (Call op hk k)  =
    join . halg . fmap (eval halg . k) . hmap (eval halg . hk) $ op

    -- This version is marginally slower:
    -- join . halg . hmap (eval halg . hk) . fmap (eval halg . k) $ op

-- Universal property from the GADT, Functorial Algebra
fold :: forall f effs a . Functor f
  => (forall x . (Effs effs f) (f x) -> f x)
  -> (forall x . x -> f x)
  -> Prog effs a -> f a
fold falg gen (Return x) = gen x
fold falg gen (Call op hk k) =
  falg ((fmap (fold falg gen . k) . hmap (fold falg gen . hk)) op)

{-# INLINE call #-}
call :: forall sub sup a . (Member sub sup, HFunctor sub) => sub (Prog sup) (Prog sup a) -> Prog sup a
call x = Call (inj x) id id

{-# INLINE prjCall #-}
prjCall :: forall sub sup a . Member sub sup => Prog sup a -> Maybe (sub (Prog sup) (Prog sup a))
-- prjCall (Call op) = prj op
prjCall (Call op hk k) = prj (hmap hk . fmap k $ op)
prjCall _              = Nothing

progAlg :: Effs sig (Prog sig) a -> Prog sig a
progAlg x = Call x id return
