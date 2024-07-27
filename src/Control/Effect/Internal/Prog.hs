{-|
Module      : Control.Effect.Internal.Prog
Description : Program constructors and deconstructors
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Internal.Prog where
import Control.Effect.Internal.Effs

import Data.HFunctor
import Control.Monad

-- | A family of programs that may contain at least the effects in @effs@ in any
-- order.
type Progs effs -- ^ A list of effects the program may use
           a    -- ^ The return value of the program
  = forall effs' . Members effs effs' => Prog effs' a

-- | A program that contains at most the effects in @effs@,
-- to be processed by a handler in the exact order given in @effs@.
data Prog (effs :: [Effect]) a where
  Return :: a -> Prog sigs a
  Call  :: forall sigs a f x
        .  Functor f
        => (Effs sigs) f x
        -> (forall x . f x -> Prog sigs x)
        -> (x -> Prog sigs a)
        -> Prog sigs a

-- The `Call` constructor is an encoding of `Call'` where:
-- Call'   :: (Effs sigs) (Prog sigs) (Prog sigs a) -> Prog sigs a
-- Call' x ~= Call x id return

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

-- | Weaken a program of type @Prog effs a@ so that it can be used in
-- place of a program of type @Prog effs a@, when every @effs@ is a member of @effs'@.
weakenProg :: forall effs effs' a
  .  Injects effs effs'
  => Prog effs a -> Prog effs' a
weakenProg (Return x) = Return x
weakenProg (Call op hk k)   =
    Call (injs op) (weakenProg @effs @effs' . hk) (weakenProg @effs @effs' . k)


-- | Evaluate a program using the supplied algebra. This is the
-- universal property from initial monad @Prog sig a@ equipped with
-- the algebra @Eff effs m -> m@.
eval :: forall effs m a . Monad m
  => Algebra effs m
  -> Prog effs a -> m a
eval halg (Return x) = return x
eval halg (Call op hk k)  =
    join . halg . fmap (eval halg . k) . hmap (eval halg . hk) $ op

    -- This version is marginally slower:
    -- join . halg . hmap (eval halg . hk) . fmap (eval halg . k) $ op

-- | Fold a program using the supplied generator and algebra. This is the
-- universal property from the underlying GADT.
fold :: forall f effs a . Functor f
  => (forall x . (Effs effs f) (f x) -> f x)
  -> (forall x . x -> f x)
  -> Prog effs a -> f a
fold falg gen (Return x) = gen x
fold falg gen (Call op hk k) =
  falg ((fmap (fold falg gen . k) . hmap (fold falg gen . hk)) op)

-- | Construct a program of type @Prog effs a@ using an operation of type @eff (Prog effs) (Prog effs a)@, when @eff@ is a member of @effs@.
{-# INLINE call #-}
call :: forall eff effs a . (Member eff effs, HFunctor eff) => eff (Prog effs) (Prog effs a) -> Prog effs a
call x = Call (inj x) id id

-- | Attempt to project an operation of type @eff (Prog effs) (Prog effs a)@.
{-# INLINE prjCall #-}
prjCall :: forall eff effs a . Member eff effs => Prog effs a -> Maybe (eff (Prog effs) (Prog effs a))
prjCall (Call op hk k) = prj (hmap hk . fmap k $ op)
prjCall _              = Nothing

-- | Construct a program from an operation in a union.
{-# INLINE progAlg #-}
progAlg :: Effs sig (Prog sig) a -> Prog sig a
progAlg x = Call x id return
