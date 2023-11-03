{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Redundant return" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Fuse foldr/fmap" #-}

module Effective where

import Prelude hiding (or)

import Data.Tuple (swap)
import Data.Kind ( Type, Constraint )

import Data.List.TypeLevel
import Data.Functor.Composes
import Data.HFunctor
import Data.HFunctor.HComposes
import Data.CutList

import Control.Applicative
import Control.Arrow
import Control.Monad ( join, ap, liftM, replicateM)
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class (MonadTrans, lift)
import Control.Monad.Identity
import qualified Control.Monad.Trans.State.Lazy as S

import Data.SOP.Constraint ( All )

type Effect = (Type -> Type) -> (Type -> Type)
type Signature = Type -> Type

type Eff :: Signature -> Effect
data Eff sig f x
  = Alg (sig x)
  | Scp (sig (f x))
  deriving Functor

instance Functor sig => HFunctor (Eff sig) where
  hmap h (Alg x) = Alg x
  hmap h (Scp x) = Scp (fmap h x)

type Effs :: [Signature] -> Effect
data Effs sigs f a where
  Eff  :: Functor sig => Eff sig f a -> Effs (sig ': sigs) f a
  Effs :: Effs sigs f a -> Effs (sig ': sigs) f a

instance Functor f => Functor (Effs sigs f) where
  fmap f (Eff x)  = Eff (fmap f x)
  fmap f (Effs x) = Effs (fmap f x)

instance HFunctor (Effs sigs) where
  hmap h (Eff x)  = Eff (hmap h x)
  hmap h (Effs x) = Effs (hmap h x)

habsurd' :: Effs '[] f x -> a
habsurd' = error "habsurd!"

data Nat = Z | S Nat

type P :: Nat -> Type
data P n = P
-- injecting/projecting at a specified position P n

-- Find an index of an element in a `list'
-- The element must exist
-- This closed type family disambiguates otherwise overlapping
-- instances
type family ElemIndex (x :: a) (xs :: [a]) :: Nat where
  ElemIndex x (x ': xs) = Z
  ElemIndex x (_ ': xs) = S (ElemIndex x xs)

class (Functor sig, HFunctor (Effs sigs)) => Member' sig sigs (n :: Nat) where
  inj' :: P n -> Eff sig f a -> Effs sigs f a
  prj' :: P n -> Effs sigs f a -> Maybe (Eff sig f a)


instance (Functor sig, (sigs' ~ (sig ': sigs))) => Member' sig sigs' Z where
  inj' :: (Functor sig, sigs' ~ (sig : sigs)) => P Z -> Eff sig f a -> Effs sigs' f a
  inj' _ = Eff

  prj' :: (Functor sig, sigs' ~ (sig : sigs)) => P Z -> Effs sigs' f a -> Maybe (Eff sig f a)
  prj' _ (Eff x) = Just x
  prj' _ _        = Nothing

instance (sigs' ~ (sig' ': sigs), Functor sig, Member' sig sigs n) => Member' sig sigs' (S n) where
  inj' _ = Effs . inj' (P :: P n)

  prj' _ (Eff _)  = Nothing
  prj' _ (Effs x) = prj' (P :: P n) x

type Member :: Signature -> [Signature] -> Constraint
class (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj :: Eff sig f a -> Effs sigs f a
  prj :: Effs sigs m a -> Maybe (Eff sig m a)

instance (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj = inj' (P :: P (ElemIndex sig sigs))
  prj = prj' (P :: P (ElemIndex sig sigs))

type family Members (xs :: [Signature]) (xys :: [Signature]) :: Constraint where
  Members '[] xys       = ()
  Members (x ': xs) xys = (Member x xys, Members xs xys, Injects (x ': xs) xys)

-- Injects xs ys means that all of xs is in xys
-- Some other effects may be in xys, so xs <= ys
type Injects :: [Signature] -> [Signature] -> Constraint
class Injects xs xys where
  injs :: Effs xs f a -> Effs xys f a

instance Injects '[] xys where
  injs :: Effs '[] f a -> Effs xys f a
  injs = habsurd'

instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

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
  hinl = habsurd'

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
  hinl (Effs x) = Effs (hinl @xs @ys x) -- hinl @xs @ys _

  hinr :: Effs ys f a -> Effs ((x : xs) :++ ys) f a
  hinr = Effs . hinr @xs @ys

  houtl :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs (x ': xs) f a)
  houtl (Eff x)  = Just (Eff x)
  houtl (Effs x) = fmap Effs (houtl @xs @ys x)

  houtr :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs ys f a)
  houtr (Eff x)  = Nothing
  houtr (Effs x) = houtr @xs @ys x

---------------------------------------
data Prog (sigs :: [Signature]) a where
  Return :: a -> Prog sigs a
  Call   :: (Effs sigs) (Prog sigs) (Prog sigs a) -> Prog sigs a

instance Functor (Prog sigs) where
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap = liftM

instance Applicative (Prog effs) where
  pure :: a -> Prog effs a
  pure  = Return

  (<*>) :: Prog effs (a -> b) -> Prog effs a -> Prog effs b
  (<*>) = ap

instance Monad (Prog effs) where
  Return x >>= f = f x
  Call op  >>= f = Call (fmap (>>= f) op)

-- Universal property from initial monad `Prog sig a` equipped with
-- `sig m -> m`
eval :: Monad m
  => (forall x . Effs effs m x -> m x)
  -> Prog effs a -> m a
eval halg (Return x) = return x
eval halg (Call op)  =
  join (halg ((fmap (eval halg) . hmap (eval halg)) op))

-- Universal property from the GADT, Functorial Algebra
fold :: Functor f
  => (forall x . (Effs effs f) (f x) -> f x)
  -> (forall x . x -> f x)
  -> Prog effs a -> f a
fold falg gen (Return x) = gen x
fold falg gen (Call op)  =
  falg ((fmap (fold falg gen) . hmap (fold falg gen)) op)

injCall :: Member sub sup => Eff sub (Prog sup) (Prog sup a) -> Prog sup a
injCall = Call . inj

-- injCall :: forall sub sup a . (Functor sub, Injects '[sub] sup) => Eff sub (Prog sup) (Prog sup a) -> Prog sup a
-- injCall = Call . (injs  @'[sub] @sup) . Eff

prjCall :: Member sub sup => Prog sup a -> Maybe (Eff sub (Prog sup) (Prog sup a))
prjCall (Call op) = prj op
prjCall _         = Nothing

type Handler
  :: [Signature]                         -- effs  : input effects
  -> [(Type -> Type) -> (Type -> Type)]  -- t     : monad transformer
  -> [Type -> Type]                      -- f     : carrier type
  -> [Signature]                         -- oeffs : output effects
  -> Type
data Handler effs ts fs oeffs =
  (All Functor fs, All MonadTrans ts) =>
  Handler
  { run  :: forall m . Monad m 
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . HComps ts m x -> m (Comps fs x))

  , malg :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . Effs effs (HComps ts m) x -> (HComps ts m) x)

  , mfwd :: forall m sig . Monad m
         => (forall x . Effs sig m x -> m x)
         -> (forall x . Effs sig (HComps ts m) x -> HComps ts m x)
  }

handler
  :: (MonadTrans t, HFunctor t, Functor f)
  => (forall m a . Monad m => t m a -> m (f a)) 
  -> (forall m . Monad m 
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs (t m) x -> t m x))
  -> (forall m sigs . Monad m 
    => (forall x . Effs sigs m x -> m x)
    -> (forall x . Effs sigs (t m) x -> t m x))
  -> Handler effs '[t] '[f] oeffs
handler runMonadT monadAlg monadFwd
  = Handler 
      (const (fmap comps . runMonadT . hdecomps))
      (\oalg -> hcomps . monadAlg oalg . hmap hdecomps)
      (\alg  -> hcomps . monadFwd alg . hmap hdecomps)

interp
  :: (forall m . Monad m
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs m x -> m x))
  -> Handler effs '[] '[] oeffs
interp monadAlg
  = Handler
      (const (\(HNil x) -> fmap CNil x))
      (\oalg -> HNil . monadAlg oalg . hmap (\(HNil x) -> x))
      (\alg  -> HNil . alg . hmap (\(HNil x) -> x))

type Fuse :: 
  [Signature] -> [Signature] -> [Signature] ->
  [Signature] -> [Signature] ->
  [(Type -> Type) -> (Type -> Type)] ->
  [(Type -> Type) -> (Type -> Type)] ->
  [Type -> Type] ->
  [Type -> Type] -> Constraint
class Fuse eff12 oeff1 oeff2 eff1 eff2 ts1 ts2 fs1 fs2 where
  fuse 
    :: ( Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2
       , Injects eff12 eff2
       , All Functor (fs2 :++ fs1)
       , All MonadTrans (ts1 :++ ts2)
       , HExpose ts1
       , Expose fs2
       )
    => Handler eff1 ts1 fs1 (oeff1 :++ eff12)
    -> Handler eff2 ts2 fs2 oeff2
    -> Handler (eff1 :++ eff2) (ts1 :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)

-- If this were `Monad (HComposes ts2 m)` it would be illegal since
-- type families cannot appear as instance heads. We get around this by using `HComps` instead.
instance (forall m . Monad m => Monad (HComps ts2 m)) => Fuse eff12 oeff1 oeff2 eff1 eff2 '[] ts2 fs1 fs2 where
  fuse
    :: (forall (m :: Type -> Type). Monad m => Monad (HComps ts2 m),
      Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2,
      Injects eff12 eff2, All Functor (fs2 :++ fs1),
      All MonadTrans ('[] :++ ts2), HExpose '[], Expose fs2)
    => Handler eff1 '[] fs1 (oeff1 :++ eff12) -> Handler eff2 ts2 fs2 oeff2
    -> Handler (eff1 :++ eff2) ('[] :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)
  fuse (Handler run1 malg1 mfwd1) (Handler run2 malg2 mfwd2) =
    Handler run malg mfwd where
      run  :: forall m . Monad m
        => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
        -> (forall x . HComps ('[] :++ ts2) m x -> m (Comps (fs2 :++ fs1) x))
      run oalg
        = fmap unexpose
        . run2 (oalg . hinr @oeff1 @oeff2)
        . run1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                      (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2))
        . hexpose

      malg :: forall m sig . Monad m
        => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
        -> (forall x . Effs (eff1 :++ eff2) (HComps ('[] :++ ts2) m) x -> HComps ('[] :++ ts2) m x)
      malg oalg
        = hunexpose @'[]
        . heither @eff1 @eff2
            ( malg1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                           (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2)))
            ( mfwd1 (malg2 (oalg . hinr @oeff1 @oeff2)))
        . hmap (hexpose @'[])

      mfwd
        :: forall m sig . Monad m
        => (forall x. Effs sig m x -> m x)
        -> forall x. Effs sig (HComps ts2 m) x -> HComps ts2 m x
      mfwd alg
        = hunexpose @'[]
        . mfwd1 (mfwd2 alg)
        . hmap (hexpose @'[])

instance (forall m . Monad m => Monad (HComps ts2 m)) => Fuse eff12 oeff1 oeff2 eff1 eff2 (t1 ': ts1) ts2 fs1 fs2 where
  fuse :: (forall (m :: Type -> Type). Monad m => Monad (HComps ts2 m),
    Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2,
    Injects eff12 eff2, All Functor (fs2 :++ fs1),
    All MonadTrans ((t1 : ts1) :++ ts2), HExpose (t1 : ts1),
    Expose fs2) => Handler eff1 (t1 : ts1) fs1 (oeff1 :++ eff12)
      -> Handler eff2 ts2 fs2 oeff2
      -> Handler (eff1 :++ eff2) ((t1 : ts1) :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)
  fuse (Handler run1 malg1 mfwd1) (Handler run2 malg2 mfwd2) =
    Handler run malg mfwd where
    run  :: forall m . Monad m
      => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
      -> (forall x . HComps ((t1 ': ts1) :++ ts2) m x -> m (Comps (fs2 :++ fs1) x))
    run oalg
      = fmap unexpose
      . run2 (oalg . hinr @oeff1 @oeff2)
      . run1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                    (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2))
      . hexpose

    malg :: forall m sig . Monad m
      => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
      -> (forall x . Effs (eff1 :++ eff2) (HComps ((t1 ': ts1) :++ ts2) m) x -> HComps ((t1 ': ts1) :++ ts2) m x)
    malg oalg
      = hunexpose @(t1 ': ts1)
      . heither @eff1 @eff2
          ( malg1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                         (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2)))
          ( mfwd1 (malg2 (oalg . hinr @oeff1 @oeff2)))
      . hmap (hexpose @(t1 ': ts1))

    mfwd
      :: forall m sig . Monad m
      => (forall x. Effs sig m x -> m x)
      -> forall x. Effs sig (HComps ((t1 ': ts1) :++ ts2) m) x -> HComps ((t1 ': ts1) :++ ts2) m x
    mfwd alg
      = hunexpose @(t1 ': ts1)
      . mfwd1 (mfwd2 alg)
      . hmap (hexpose @(t1 ': ts1))

(<&>)
  :: forall eff1 eff2 ts1 ts2 fs1 fs2
  .  (Fuse '[] '[] '[] eff1 eff2 ts1 ts2 fs1 fs2
     , Append eff1 eff2
     , All Functor (fs2 :++ fs1)
     , All MonadTrans (ts1 :++ ts2)
     , HExpose ts1
     , Expose fs2
     )
  => Handler eff1 ts1 fs1 '[]
  -> Handler eff2 ts2 fs2 '[]
  -> Handler (eff1 :++ eff2) (ts1 :++ ts2) (fs2 :++ fs1) '[]
(<&>) = fuse @'[] @'[] @'[] @eff1 @eff2 @ts1 @ts2 @fs1 @fs2


handle :: (Monad (HComps ts Identity), Recompose fs)  =>
  Handler effs ts fs '[] -> Prog effs a -> Composes fs a
handle (Handler run malg mfwd)
  -- = runIdentity . run @Identity habsurd' . eval (malg @Identity habsurd')
  = recompose . runIdentity . run @Identity habsurd' . eval (malg @Identity habsurd')

handle'
  :: (Monad (HComps ts (Prog oeffs)), Recompose fs)
  => Handler effs ts fs oeffs -> Prog effs a -> Prog oeffs (Composes fs a)
handle' (Handler run malg mfwd)
  = fmap recompose . run (Call . fmap return) . eval (malg (Call . fmap return))

-- The parameters sig and sig' should always be instantiated manually. Good luck.
handleOne
  :: forall sig sig' eff oeffs ts fs a m
  . ( Injects oeffs sig', Injects sig sig', Append eff sig
  , Monad (HComps ts (Prog sig')), Recompose fs)
  => Handler eff ts fs oeffs -> Prog (eff :++ sig) a -> Prog sig' (Composes fs a)
handleOne (Handler run malg mfwd)
  = fmap recompose
  . run (Call . injs . fmap return)
  . eval (heither @eff @sig (malg @(Prog sig') (Call . injs . fmap return))
                            (mfwd @(Prog sig') (Call . injs . fmap return)))

-----------------------------------------
-- Example: Exceptions
-----------------------------------------

data Throw k where
  Throw :: Throw k
  deriving Functor

data Catch k where
  Catch :: k -> k -> Catch k
  deriving Functor

-- Either works:
-- throw :: Members '[Throw] sig => Prog sig a
throw :: Member Throw sig => Prog sig a
throw = injCall (Alg Throw)

-- also Members '[Catch] sig works
-- catch :: Member Catch sig => Prog sig a -> Prog sig a -> Prog sig a
-- catch p q = injCall (Scp (Catch (fmap return p) (fmap return q)))
-- catch :: Injects '[Catch] sig => Prog sig a -> Prog sig a -> Prog sig a
catch :: Member Catch sig => Prog sig a -> Prog sig a -> Prog sig a
catch p q = injCall (Scp (Catch (fmap return p) (fmap return q)))

instance HFunctor MaybeT where
  hmap h (MaybeT mx) = MaybeT (h mx)

exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
exceptAlg oalg eff
  | Just (Alg Throw) <- prj eff
      = MaybeT (return Nothing)
  | Just (Scp (Catch p q)) <- prj eff
      = MaybeT $ do mx <- runMaybeT p
                    case mx of
                      Nothing -> runMaybeT q
                      Just x  -> return (Just x)

exceptFwd
  :: Monad m
  => (forall x. Effs sigs m x -> m x)
  -> (forall x. Effs sigs (MaybeT m) x -> MaybeT m x)
exceptFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
exceptFwd alg (Eff (Scp x)) = MaybeT (alg (Eff (Scp (fmap runMaybeT x))))
exceptFwd alg (Effs effs)   = exceptFwd (alg . Effs) effs

except :: Handler [Throw, Catch] '[MaybeT] '[Maybe] oeff
except = Handler
  (const (fmap comps . runMaybeT . hdecomps))
  (\oalg -> hcomps . exceptAlg oalg . hmap hdecomps)
  (\alg  -> hcomps . exceptFwd alg . hmap hdecomps)



-----------------------------------------
-- Exceptions
-----------------------------------------

monus 
  :: Members [Throw, Catch] sig
  => Int -> Int -> Prog sig Int
monus x y = do if x < y then throw else return (x - y)

safeMonus 
  :: Members [Throw, Catch] sig
  => Int -> Int -> Prog sig Int
safeMonus x y = do catch (monus x y) (return 0)


exampleExcept1, exampleExcept2, exampleExcept3, exampleExcept4 :: Maybe Int
exampleExcept1 = handle except (monus 2 4)
exampleExcept2 = handle except (monus 4 2)
exampleExcept3 = handle except (safeMonus 2 4)
exampleExcept4 = handle except (safeMonus 4 2)
-- ghci> exampleExcept1
-- Nothing
-- ghci> exampleExcept2
-- Just 2
-- ghci> exampleExcept3
-- Just 0
-- ghci> exampleExcept4
-- Just 2



-- multiple semantics such as retry after handling is difficult in MTL
-- without resorting to entirely different newtype wrapping through
-- the whole program.
-- TODO: joinAlg
retryAlg :: Monad m
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
retryAlg oalg eff
  | Just (Alg Throw) <- prj eff
      = MaybeT (return Nothing)
  | Just (Scp (Catch p q)) <- prj eff = MaybeT $ loop p q
      where
        loop p q =
          do mx <- runMaybeT p
             case mx of
               Nothing -> do my <- runMaybeT q
                             case my of
                               Nothing -> return Nothing
                               Just y  -> loop p q
               Just x  -> return (Just x)

-- retry :: Handler [Throw, Catch] '[MaybeT] '[Maybe] oeffs
-- retry = Handler
--   (const (fmap comps . runMaybeT . hdecomps))
--   (\oalg -> hcomps . retryAlg oalg . hmap hdecomps)
--   (\alg  -> hcomps . exceptFwd alg . hmap hdecomps)

retry :: Handler [Throw, Catch] '[MaybeT] '[Maybe] oeffs
retry = handler runMaybeT retryAlg exceptFwd

-- -----------------------------------------
-- State
-- -----------------------------------------
--
data Put s k where
  Put :: s -> k -> Put s k
  deriving Functor

data Get s k where
  Get :: (s -> k) -> Get s k
  deriving Functor

data Local s x where
  Local :: s -> x -> Local s x
  deriving Functor

type State s = '[Put s, Get s, Local s]

put :: Member (Put s) sig => s -> Prog sig ()
put s = injCall (Alg (Put s (return ())))

get :: Member (Get s) sig => Prog sig s
get = injCall (Alg (Get return))

local :: Member (Local s) sig => s -> Prog sig a -> Prog sig a
local s p = injCall (Scp (Local s (fmap return p)))


instance HFunctor (S.StateT s) where
  hmap h (S.StateT p) = S.StateT (\s -> h (p s))

stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s, Local s] (S.StateT s m) x -> S.StateT s m x)
stateAlg oalg eff
  | Just (Alg (Put s p)) <- prj eff =
      do S.put s
         return p
  | Just (Alg (Get p)) <- prj eff =
      do s <- S.get
         return (p s)
  | Just (Scp (Local s (S.StateT p))) <- prj eff =
      lift (fmap fst (p s))

stateFwd
  :: Monad m
  => (forall x. Effs sig m x -> m x)
  -> (forall x. Effs sig (S.StateT s m) x -> S.StateT s m x)
stateFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
stateFwd alg (Eff (Scp x)) = S.StateT (\s -> (alg (Eff (Scp (fmap (flip S.runStateT s) x)))))
stateFwd alg (Effs effs)   = stateFwd (alg . Effs) effs

state :: s -> Handler [Put s, Get s, Local s] '[S.StateT s] '[((,) s)] oeff
state s = handler (fmap swap . flip S.runStateT s) stateAlg stateFwd

-- -----------------------------------------

incr
  :: Members [Put Int, Get Int] sig
  => Prog sig ()
incr = do x <- get
          put @Int (x + 1)

decr
  :: Members [Put Int, Get Int, Throw] sig
  => Prog sig ()
decr = do x <- get
          if (x > 0)
            then put @Int (x - 1)
            else throw

exampleState :: (Int, ())
exampleState = handle (state 41) incr
-- ghci> exampleState
-- (42,())

-----------------------------------------
-- Composition of State and Exceptions : Local/Global State
-----------------------------------------

catchDecr
  :: Members [Put Int, Get Int, Throw, Catch] sig
  => Prog sig ()
catchDecr = do
  decr
  catch (decr >> decr)
        (return ())


globalState
  :: s -> Handler [Throw, Catch, Put s, Get s, Local s]
          [MaybeT,  S.StateT s]
          [((,) s), Maybe] '[]
globalState s = except <&> state s

exampleGlobalState :: (Int, Maybe ())
exampleGlobalState = handle (globalState 2) catchDecr
-- This is global state because the `Int` is decremented
-- twice before the exception is thrown.
--
-- ghci> exampleGlobalState
-- (0,Just ())


localState
  :: s -> Handler
          [Put s, Get s, Local s, Throw, Catch]
          [S.StateT s, MaybeT]
          [Maybe, ((,) s)]
          '[]
localState s = state s <&> except

exampleLocalState :: Maybe (Int, ())
exampleLocalState = handle (localState 2) catchDecr
-- With local state, the state is reset to its value
-- before the catch where the exception was raised.
--
-- ghci> exampleLocalState
-- Just (1,())

catchDecr'
  :: Members [Put Int, Get Int, Throw, Catch] sig
  => Prog sig ()
catchDecr' = do
  decr
  catch (decr >> decr)
        (replicateM 44 incr >> return ())

-- For instance you might want to allocate a bit more memory ...
-- and a bit more ... and so on.
exampleRetry1 :: (Int, Maybe ())
exampleRetry1 = handle (retry <&> state 2) catchDecr'


-----------------------------------------
-- Example: Nondeterminism
data Stop a :: Type where
  Stop :: Stop a
  deriving Functor

stop :: forall sig a . Member Stop sig => Prog sig a
stop  = injCall (Alg Stop)

data Or a :: Type where
  Or :: a -> a -> Or a
  deriving Functor

or :: forall scp sig a . Member Or sig => Prog sig a -> Prog sig a -> Prog sig a
or x y = injCall (Alg (Or x y))

instance (Members [Or, Stop] sig) => Alternative (Prog sig) where
  empty :: Members [Or, Stop] sig => Prog sig a
  empty = stop

  (<|>) :: Members [Or, Stop] sig => Prog sig a -> Prog sig a -> Prog sig a
  (<|>) = or

select :: Members [Or, Stop] sig => [a] -> Prog sig a
select = foldr (or . return) stop


newtype AListT m e a = AListT { runAListT :: m (Either e (a, ListT m a)) }
  deriving Functor

newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }
  deriving Functor

runListT' :: Monad m => ListT m a -> m [a]
runListT' (ListT mmxs) =
  do mxs <- mmxs
     case mxs of
       Nothing         -> return []
       Just (x, mmxs') -> (x :) <$> runListT' mmxs'

instance HFunctor ListT where
  hmap :: (Functor f, Functor g) => (forall x1. f x1 -> g x1) -> ListT f x -> ListT g x
  hmap h (ListT mx) = ListT (fmap (fmap (fmap (hmap h))) (h mx))

foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT k ys (ListT mxs) = mxs >>= maybe ys (\(x,xs) -> k x (foldListT k ys xs))

instance Monad m => Applicative (ListT m) where
  pure x = ListT (pure (Just (x, empty)))
  (<*>) = ap

instance Monad m => Monad (ListT m) where
  (>>=) :: Monad m => ListT m a -> (a -> ListT m b) -> ListT m b
  m >>= f = ListT $ foldListT (\x l -> runListT $ f x <|> ListT l) (return Nothing) m

instance Monad m => Alternative (ListT m) where
  empty = ListT (return Nothing)
  (<|>) :: Monad m => ListT m a -> ListT m a -> ListT m a
  ListT mxs <|> ListT mys = ListT $
    mxs >>= maybe mys (return . Just . second (<|> ListT mys))

instance MonadTrans ListT where
  lift :: Monad m => m a -> ListT m a
  lift = ListT . liftM (\x -> Just (x, empty))

nondetAlg
  :: (MonadTrans t, Alternative (t m) , Monad m)
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Stop , Or] (t m) x -> t m x)
nondetAlg oalg eff
  | Just (Alg Stop)     <- prj eff = empty
  | Just (Alg (Or x y)) <- prj eff = return x <|> return y

nondetFwd
  :: (Monad m)
  => (forall x. Effs sig m x -> m x)
  -> forall x. Effs sig (ListT m) x -> ListT m x
nondetFwd alg (Eff (Alg x)) = lift  (alg (Eff (Alg x)))
nondetFwd alg (Eff (Scp x)) = ListT (alg (Eff (Scp (fmap runListT x))))
nondetFwd alg (Effs effs)   = nondetFwd (alg . Effs) effs

nondet :: Handler [Stop, Or] '[ListT] '[[]] oeff
nondet = handler runListT' nondetAlg nondetFwd

-------------------------------
-- Example: Backtracking (and Culling?)
data Once a :: Type where
  Once :: a -> Once a
  deriving Functor

once :: forall alg sig a . Member Once sig => Prog sig a -> Prog sig a
once p = injCall (Scp (Once (fmap return p)))

-- Everything can be handled together. Here is the non-modular way
-- list :: (Member (Or) sig, Member (Stop) sig, Member (Once) sig) => Prog sig a -> [a]
list :: Prog [Stop, Or, Once] a -> [a]
list = eval halg where
  halg :: Effs [Stop, Or, Once] [] a -> [a]
  halg op
    | Just (Alg Stop)          <- prj op = []
    | Just (Alg (Or x y))      <- prj op = [x, y]
    | Just (Scp (Once []))     <- prj op = []
    | Just (Scp (Once (x:xs))) <- prj op = [x]

backtrackAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Stop, Or, Once] (ListT m) x -> ListT m x)
backtrackAlg oalg op
  | Just (Alg Stop)     <- prj op = empty
  | Just (Alg (Or x y)) <- prj op = return x <|> return y
  | Just (Scp (Once p)) <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))

-- We can also define by composition
joinAlg :: forall sig1 sig2 oeff t m x .
  ( Monad m, Append sig1 sig2 )
  => ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig1 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig2 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs (sig1 :++ sig2) (t m) x -> t m x))
joinAlg falg galg oalg =
  heither @sig1 @sig2 (falg oalg) (galg oalg)

backtrackOnceAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Once] (ListT m) x -> ListT m x)
backtrackOnceAlg oalg op
  | Just (Scp (Once p)) <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))

backtrackAlg'
  :: Monad m => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Stop, Or, Once] (ListT m) x -> ListT m x)
backtrackAlg' = joinAlg nondetAlg backtrackOnceAlg
-- TODO: The alternative with monad transformers is painful.
-- TODO: this becomes interesting when different search strategies are used


backtrackFwd
  :: (Monad m)
  => (forall x. Effs sig m x -> m x)
  -> forall x. Effs sig (ListT m) x -> ListT m x
backtrackFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
backtrackFwd alg (Eff (Scp x)) = ListT (alg (Eff (Scp (fmap runListT x))))
backtrackFwd alg (Effs effs)   = backtrackFwd (alg . Effs) effs

backtrack :: Handler [Stop, Or, Once] '[ListT] '[[]] oeff
backtrack = handler runListT' backtrackAlg' backtrackFwd

-----------------------------------------
-- Nondet
-----------------------------------------
knapsack
  :: Members [Stop, Or] sig
  => Int -> [Int] -> Prog sig [Int]
knapsack w vs
  | w <  0 = stop
  | w == 0 = return []
  | w >  0 = do v <- select vs
                vs' <- knapsack (w - v) vs
                return (v : vs')


-- `list` is not a modular handler and uses `eval` directly
exampleNondet1 :: [[Int]]
exampleNondet1 = list $ knapsack 3 [3, 2, 1]
-- [[3],[2,1],[1,2],[1,1,1]]

-- `nondet` is a modular handler but does not
-- handle `once`. Here it is immaterial because `once`
-- does not appear in the program
exampleNondet2 :: [[Int]]
exampleNondet2 = handle nondet $ knapsack 3 [3, 2, 1]
-- [[3],[2,1],[1,2],[1,1,1]]

-- `backtrack` is modular, and is furthermore simply
-- the joining of the nondet algebra with an algebra
-- for once
exampleNondet3 = handle backtrack $ knapsack 3 [3, 2, 1]
-- [[3],[2,1],[1,2],[1,1,1]]


-----------------------------------------
-- Example: Parsing
char :: Members [Get [Char], Put [Char], Stop, Or] sig => Prog sig Char
char = do xxs <- get
          case xxs of
            []     -> stop
            (x:xs) -> do put xs
                         return x

symbol :: Members [Get [Char], Put [Char], Stop, Or] sig => Char -> Prog sig Char
symbol c = do c' <- char
              if c == c'
                then return c
                else stop

digit :: Members [Get [Char], Put [Char], Stop, Or] sig => Prog sig Char
digit = foldr (<|>) stop (fmap symbol ['0' .. '9'])


int, expr, term, fact :: Members [Get [Char], Put [Char], Stop, Or] sig => Prog sig Int
int  = do ds <- some digit ; return (read ds)
expr = or (do i <- term ; symbol '+' ; j <- expr ; return (i + j))
          (do i <- term ; return i)
term = or (do i <- fact ; symbol '*' ; j <- term ; return (i * j))
          (do i <- fact ; return i)
fact = or (int)
          (do symbol '(' ; i <- expr ; symbol ')' ; return i)

-- int', expr', term', fact' :: forall sig .
--   ( Member ((Get [Char])) sig
--   , Member ((Put [Char])) sig
--   , Member (Stop) sig
--   , Member (Or) sig)
--   => Prog sig Int
--
-- int'  = read <$> some digit
-- expr' = ((+) <$> term' <* symbol '+' <*> expr') <|> term'
-- term' = ((*) <$> fact' <* symbol '*' <*> term') <|> fact'
-- fact' = int <|> (symbol '(' *> expr' <* symbol ')')

-- A parser!
parse
  :: text -> Prog [Put text, Get text, Local text, Stop, Or] a
  -> [(text, a)]
parse cs p  = handle (state cs <&> nondet) p

exampleParse1 = parse "2+3*5" expr
-- ghci> exampleParse
-- [("",17),("*5",5),("+3*5",2)]

-- Not a parser!
notParse
  :: text -> Prog [Stop, Or, Put text, Get text, Local text] a
  -> (text, [a])
notParse cs p = handle (nondet <&> state cs) p

exampleNotParse :: (String, [Int])
exampleNotParse = notParse "2+3*5" expr
-- ghci> exampleNotParse
-- ("",[])

-------------------------------
-- CutFail
-------------------------------
{-
Idea:

Nondeterminism consists of just or and stop.
A model of this is lists, using the list monad transformer.

If we want a notion of backtracking, we must include
a new operation, like `try`, which can be interpreted
as executing `once`, many times etc.

One way to interpret `once` is into the list monad directly.
An alternative is to interpet `once` into `cutFail` and `cutCall`,
which can then be interpreted using a `CutList`.
-}

data CutFail a :: Type where
  CutFail :: CutFail a
  deriving Functor


cut :: (Members [Or, Stop, CutFail] sig) => Prog sig ()
cut = skip <|> cutFail

cutFail :: Member CutFail sig => Prog sig a
cutFail = injCall (Alg CutFail)

data CutCall a :: Type where
  CutCall :: a -> CutCall a
  deriving Functor

cutCall :: Member CutCall sig => Prog sig a -> Prog sig a
cutCall p = injCall (Scp (CutCall (fmap return p)))

skip :: Monad m => m ()
skip = return ()

callAlg :: Monad m => CutListT m a -> CutListT m a
callAlg (CutListT mxs) = CutListT $
  do xs <- mxs
     case xs of
       x :<< mys -> return (x :<< runCutListT (callAlg (CutListT mys)))
       NilT      -> return NilT
       ZeroT     -> return NilT   -- clear the cut flag at the boundary of call

cutListFwd
  :: Monad m
  => (forall x . Effs sig m x -> m x)
  -> (forall x . Effs sig (CutListT m) x -> CutListT m x)
cutListFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
cutListFwd alg (Eff (Scp x)) = CutListT (alg (Eff (Scp (fmap runCutListT x))))
cutListFwd alg (Effs effs)   = cutListFwd (alg . Effs) effs

cutListAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> forall x. Effs [Stop, Or, CutFail, CutCall] (CutListT m) x -> CutListT m x
cutListAlg oalg op
  | Just (Alg Stop)        <- prj op = empty
  | Just (Alg (Or x y))    <- prj op = return x <|> return y
  | Just (Alg CutFail)     <- prj op = CutListT (return ZeroT)
  | Just (Scp (CutCall x)) <- prj op = callAlg x

cutList :: Handler [Stop, Or, CutFail, CutCall] '[CutListT] '[[]] oeff
cutList = handler fromCutListT' cutListAlg cutListFwd

instance HFunctor CutListT where
  hmap h (CutListT x) = CutListT (fmap (hmap h) (h x))

instance HFunctor CutListT' where
  hmap h ZeroT      = ZeroT
  hmap h NilT       = NilT
  hmap h (x :<< xs) = x :<< fmap (hmap h) (h xs)

-- TODO: Can we make it so that oeff is always a "Members"?
onceCut :: Members [CutCall, CutFail, Or] oeff => Handler '[Once] '[] '[] oeff
onceCut = interp onceCutAlg

onceCutAlg :: forall oeff m . (Monad m , Members [CutCall, CutFail, Or] oeff)
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs '[Once] (HComposes '[] m) x -> HComposes '[] m x)
onceCutAlg oalg op
  | Just (Scp (Once p)) <- prj op = cutCall' oalg' (do x <- p ; cut' oalg' ; return x)
  where
    oalg' :: forall a . Effs oeff m a -> m a
    oalg' = oalg

cut' :: (Monad m, Members [CutFail, Or] sig)
  => (forall a . Effs sig m a -> m a) -> m ()
cut' alg = (call' alg . inj) (Alg (Or (return ()) (cutFail' alg)))

cutFail' :: (Monad m, Member CutFail sig)
  => (forall a . Effs sig m a -> m a) -> m a
cutFail' alg = (call' alg . inj) (Alg CutFail)

cutCall' :: (Monad m, Member CutCall sig)
  => (forall a . Effs sig m a -> m a) -> m a -> m a
cutCall' alg p = (alg . inj) (Scp (CutCall p))

call' :: Monad m => (forall a . sig m a -> m a) -> (sig m (m a) -> m a)
call' alg x = join (alg x)


-- This example demonstrates the use of Cut
expr', term', fact' :: forall sig .
  Members [Get [Char], Put [Char], Stop, Or, CutFail, CutCall] sig
  => Prog sig Int
expr' = do i <- term'
           cutCall (or (do symbol '+' ; cut; j <- expr' ; return (i + j))
                       (do return i))
term' = do i <- fact'
           cutCall (or (do symbol '*' ; cut; j <- term' ; return (i * j))
                       (do return i))
fact' = or int
           (do symbol '(' ; i <- expr' ; symbol ')' ; return i)

onceNondet :: Handler [Once, Stop, Or, CutFail, CutCall] '[CutListT] '[[]] '[]
onceNondet = fuse @'[CutCall, CutFail, Or] @'[] onceCut cutList

-- onceEx :: (Member Or sig, Member Once sig) => Prog sig Int
onceEx :: Members [Or, Once] sig => Prog sig Int
onceEx = do x <- once (or (return 0) (return 5))
            or (return (x + 1)) (return (x + 2))

exampleOnce :: [Int]
exampleOnce = handle onceNondet onceEx
-- ghci> exampleOnce
-- [1,2]
--
-- A different parser!
parse' :: text -> Prog [Put text, Get text, Local text, Once, Stop, Or, CutFail, CutCall] a -> [(text, a)]
parse' cs p  = handle (state cs <&> onceNondet) p

exampleParse2 = parse' "2+3*5" expr'
-- ghci> exampleParse2
-- Compose [Identity ("",17)]

