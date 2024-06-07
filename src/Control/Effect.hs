{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect
  ( module Control.Effect.Type
  , Prog(..)
  , Prog'
  , Member(..)
  , Members(..)
  , handle
  , handle'
  , handler
  , handleT
  , handlerT
  , Handler (..)
  , Handler' (..)
  , injCall
  , progAlg
  , interpret'
  , eval
  -- , fuse
  , fuse'
  , joinAlg
  ) where
import Control.Effect.Type

import Data.Kind ( Constraint )
import Data.Nat

import Data.Kind ( Type )
import Data.List.Kind
import Data.Functor.Identity
import Data.Functor.Composes
    ( RComps(..), Rercompose(rercompose), RComposes, rcomps, RSplit (..))
import Data.HFunctor
import Control.Monad.Trans.Identity
import Control.Monad.Trans.TCompose
import Control.Family
import Data.HFunctor.HCompose

import Control.Monad ( join, ap, liftM )
import Control.Monad.Trans.Class

joinAlg :: forall sig1 sig2 oeff t m .
  ( Monad m, Append sig1 sig2 )
  => ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig1 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig2 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs (sig1 :++ sig2) (t m) x -> t m x))
joinAlg falg galg oalg =
  heither @sig1 @sig2 (falg oalg) (galg oalg)

---------------------------------------
type Prog' sig a = forall sig' . Members sig sig' => Prog sig' a
data Prog (sigs :: [Effect]) a where
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

weakenProg :: forall effs effs' a
  .  Injects effs effs'
  => Prog effs a -> Prog effs' a
weakenProg (Return x) = Return x
weakenProg (Call op)   =
    Call ( injs @effs @effs'
         . hmap (weakenProg @effs @effs')
         . fmap (weakenProg @effs @effs')
         $ op )

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

injCall :: Member sub sup => sub (Prog sup) (Prog sup a) -> Prog sup a
injCall = Call . inj

prjCall :: Member sub sup => Prog sup a -> Maybe (sub (Prog sup) (Prog sup a))
prjCall (Call op) = prj op
prjCall _         = Nothing

progAlg :: Effs sig (Prog sig) a -> Prog sig a
progAlg = Call . fmap return

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
-- use a proxy for t as a datatype here?
type Handler
  :: [Effect]                          -- effs  : input effects
  -> [Effect]                          -- oeffs : output effects
  -> [Type -> Type]                    -- f     : carrier type
  -> Type
data Handler effs oeffs fs
  =  forall t . (MonadTrans t, Forward effs t)
  => Handler (Handler' effs oeffs t fs)

--   => Handler (Proxy t, Handler' effs oeffs t fs)
-- data Proxy t = Proxy


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

handler
  :: (MonadTrans t, Functor f, Forward effs t)
  => (forall m a . Monad m => t m a -> m (f a))
  -> (forall m . Monad m
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs (t m) x -> t m x))
  -> Handler effs oeffs '[f]
handler run malg = Handler (Handler' (const (fmap rcomps . run)) malg)

type AlgebraT effs oeffs t = forall m.  Monad m
  => (forall x. Effs oeffs m x -> m x)
  -> (forall x. Effs effs (t m) x -> t m x)

-- The definition of `handlerT` motivates the need for a snoc list
-- in the functor carrier. Without this, we need to expose the functors
-- using `Exposes fs '[f']`, and this becomes very burdensome for the
-- end user.

-- TODO : oeffs' could be generated in Algebra effs' oeffs' t'
-- TODO: there is a nasty undefined here, see error!!
-- It could be resolved if
-- oalg :: forall m . Monad m => Algebra oeff m, since then the hole
-- can be filled, since it has type `Alegbra oeff (t m)`.
handlerT
  :: forall effs' effs oeffs t fs t' f'
  .  (Append effs' effs, ForwardT effs t', MonadTrans t, MonadTrans t', Functor f')
  => AlgebraT effs' oeffs t'
  -> (forall m a . t' m a -> m (f' a))
  -> Handler' effs oeffs t fs
  -> Handler' (effs' :++ effs) (oeffs) (TCompose t' t) (f' ': fs)
handlerT alg runT (Handler' run malg) = Handler' run' malg' where
  run' :: Monad m => Algebra (oeffs) m
       -> forall x. TCompose t' t m x -> m (RComps (f' : fs) x)
  run' oalg x = fmap RCCons (run oalg ((runT . getTCompose) x))

  malg' :: Monad m => Algebra oeffs m -> Algebra (effs' :++ effs) (TCompose t' t m)
  malg' oalg = heither @effs' @effs
    (TCompose . alg (error "oalg is not polymorphic enough") . hmap getTCompose)
    (fwdT (malg oalg))

-- TODO: A better error message for unsafePrj
interpret
  :: forall eff effs oeffs
  .  Member eff effs
  => (forall m x . eff m x -> Prog oeffs x)
  -> Handler effs oeffs '[]
interpret f = interpret' (\oalg -> eval oalg . f . unsafePrj)
  where
    unsafePrj :: Effs effs m x -> eff m x
    unsafePrj x = case prj x of Just y -> y

interpret'
  :: forall effs oeffs . (forall m . Monad m
     => (forall x . Effs oeffs m x -> m x)
     -> (forall x . Effs effs m x -> m x))
  -> Handler effs oeffs '[]
interpret' alg
  = Handler $ Handler' @effs @oeffs @IdentityT
      (const (\(IdentityT mx) -> fmap RCNil mx))
      (\oalg -> IdentityT . alg oalg . hmap runIdentityT)

-- fuse :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs fs
--   . ( effs  ~ effs1 `Union` effs2
--     , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
--     , fs    ~ fs1 :++ fs2
--     , Functor (RComps fs2)
--     , RSplit fs1
--     , Append (oeffs1 :\\ effs2) effs2
--     , Append effs1 (effs2 :\\ effs1)
--     , Injects (oeffs1 :\\ effs2) oeffs
--     , Injects (effs2 :\\ effs1) effs2
--     , Injects oeffs2 oeffs
--     , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
--     )
--   => Handler effs1 oeffs1 fs1
--   -> Handler effs2 oeffs2 fs2
--   -> Handler effs  oeffs  fs
-- fuse (Handler h1) (Handler h2) = Handler (fuse' h1 h2)

fuse'
  :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 effs oeffs t fs
  . ( effs  ~ effs1 `Union` effs2
    , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
    , t     ~ TCompose t1 t2
    , fs    ~ fs1 :++ fs2
    , Functor (RComps fs2)
    , RSplit fs1
    , Forward (oeffs1 :\\ effs2) t2
    , Forward effs2 t1
    , Append (oeffs1 :\\ effs2) effs2
    , Append effs1 (effs2 :\\ effs1)
    , Injects (oeffs1 :\\ effs2) oeffs
    , Injects (effs2 :\\ effs1) effs2
    , Injects oeffs2 oeffs
    , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
    , MonadTrans t1
    , MonadTrans t2
    )
  => Handler' effs1 oeffs1 t1 fs1
  -> Handler' effs2 oeffs2 t2 fs2
  -> Handler' effs  oeffs  t  fs
fuse' (Handler' run1 malg1)  (Handler' run2 malg2) = Handler' run malg where
  run :: forall m . Monad m => Algebra oeffs m -> forall x. t m x -> m (RComps fs x)
  run oalg
    = fmap unrsplit
    . run2 (oalg . injs)
    . run1 (weakenAlg $
        heither @(oeffs1 :\\ effs2) @effs2
          (fwd @(oeffs1 :\\ effs2) @t2 (weakenAlg oalg))  -- TODO: is fwd' really the right thing? Could we use fwd?
          (malg2 (weakenAlg oalg)))
    . getTCompose

  malg :: forall m . Monad m => Algebra oeffs m -> Algebra effs (t m)
  malg oalg
    = TCompose
    . hunion @effs1 @effs2
        (malg1 (weakenAlg $
          heither @(oeffs1 :\\ effs2) @effs2
            (fwd @(oeffs1 :\\ effs2) @t2 (weakenAlg oalg))
            (malg2 (weakenAlg oalg))))
        (fwd @effs2 @t1 (malg2 (oalg . injs)))
    . hmap getTCompose

-- (<&>) :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs fam .
--   ( All Functor fs1, All Functor fs2, All Functor (fs2 :++ fs1)
--   , Expose fs2
--   , Append effs1 (effs2 :\\ effs1)
--   , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
--   , Append (oeffs1 :\\ effs2) effs2
--   , Append (oeffs1 :\\ effs2) oeffs2
--   , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
--   , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
--   , Injects (effs2 :\\ effs1) effs2
--   , fam (Effs (oeffs1 :\\ effs2))
--   , fam (Effs effs2)
--   , effs  ~ effs1 `Union` effs2
--   , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 )
--   => Handler effs1 oeffs1 fs1 fam
--   -> Handler effs2 oeffs2 fs2 fam
--   -> Handler (effs1 `Union` effs2) ((oeffs1 :\\ effs2) `Union` oeffs2 ) (fs2 :++ fs1) fam
-- (<&>) = fuse
--
-- pipe :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 oeffs fam .
--   ( All Functor (fs2 :++ fs1)
--   , Expose fs2
--   , oeffs ~ ((oeffs1 :\\ effs2) `Union` oeffs2)
--   , Append (oeffs1 :\\ effs2) effs2
--   , Injects oeffs2 oeffs
--   , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
--   , Injects (oeffs1 :\\ effs2) oeffs
--   , fam (Effs (oeffs1 :\\ effs2)) )
--   => Handler effs1 oeffs1 fs1 fam
--   -> Handler effs2 oeffs2 fs2 fam
--   -> Handler effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (fs2 :++ fs1) fam
-- pipe (Handler h1) (Handler h2) = Handler (pipe' h1 h2)
--
-- pipe' :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 oeffs fam .
--   ( All Functor (fs2 :++ fs1)
--   , MonadTrans t1
--   , MonadTrans t2
--   , Expose fs2
--   , oeffs ~ ((oeffs1 :\\ effs2) `Union` oeffs2)
--   , Append (oeffs1 :\\ effs2) effs2
--   , Injects oeffs2 oeffs
--   , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
--   , Injects (oeffs1 :\\ effs2) oeffs
--   , fam (Effs (oeffs1 :\\ effs2)) )
--   => Handler' effs1 oeffs1 t1 fs1 fam
--   -> Handler' effs2 oeffs2 t2 fs2 fam
--   -> Handler' effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (HCompose t1 t2) (fs2 :++ fs1) fam
-- pipe' (Handler' run1 malg1 mfwd1) (Handler' run2 malg2 mfwd2) =
--   Handler' run malg mfwd where
--   run  :: forall m . Monad m
--     => (forall x . Effs ((oeffs1 :\\ effs2) `Union` oeffs2) m x -> m x)
--     -> (forall x . HCompose t1 t2 m x -> m (Comps (fs2 :++ fs1) x))
--   run oalg
--     = fmap (unexpose @fs2 @fs1)
--     . run2 (oalg . injs)
--     . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @(effs2)
--         (mfwd2 (weakenAlg oalg))
--         (malg2 (weakenAlg oalg)))
--     . getHCompose
-- 
--   malg :: forall m . Monad m
--     => (forall x . Effs ((oeffs1 :\\ effs2) `Union` oeffs2) m x -> m x)
--     -> (forall x . Effs effs1 (HCompose t1 t2 m) x -> HCompose t1 t2  m x)
--   malg oalg
--     = HCompose
--     . (malg1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
--                             (mfwd2 (weakenAlg oalg))
--                             (malg2 (weakenAlg oalg))))
--     . hmap getHCompose
-- 
--   mfwd
--     :: forall m sig . (Monad m , fam sig, HFunctor sig)
--     => (forall x. sig m x -> m x)
--     -> forall x. sig (HCompose t1 t2 m) x -> HCompose t1 t2 m x
--   mfwd alg
--     = HCompose
--     . mfwd1 (mfwd2 alg)
--     . hmap getHCompose
-- 
-- pass :: forall sig effs oeffs fs fam .
--   ( All Functor fs
--   , Append effs (sig :\\ effs)
--   , Append (oeffs :\\ sig) sig
--   , Append (oeffs :\\ sig) (sig :\\ (oeffs :\\ sig))
--   , Injects sig ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
--   , Injects oeffs ((oeffs :\\ sig) :++ sig)
--   , Injects (oeffs :\\ sig) ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
--   , Injects (sig :\\ effs) sig
--   , fam (Effs (oeffs :\\ sig))
--   , fam (Effs sig) )
--   => Handler effs oeffs fs fam
--   -> Handler (effs `Union` sig) ((oeffs :\\ sig) `Union` sig) fs fam
-- pass h = fuse h (forward @sig)
--      (\alg  -> IdentityT . alg . hmap runIdentityT)

forward :: Handler effs effs '[]
forward = Handler $ Handler'
  (const (\(IdentityT mx) -> fmap RCNil mx))
  (\oalg -> IdentityT . oalg . hmap runIdentityT)

handleT :: forall effs t fs a .
  ( MonadTrans t
  , Rercompose fs
  , Forward effs (TCompose t IdentityT) )
  => (Handler' '[] '[] IdentityT '[] -> Handler' effs '[] (TCompose t IdentityT) fs)
  -> Prog effs a -> (RComposes fs a)
handleT h = handle (Handler (h idHandler))

idHandler :: Handler' '[] '[] IdentityT '[]
idHandler = Handler' run malg where

  run :: Functor m => Algebra '[] m -> (forall x. IdentityT m x -> m (RComps '[] x))
  run _ (IdentityT x) = fmap RCNil x

  malg :: Algebra '[] m -> Algebra '[] (IdentityT m)
  malg alg = absurdEffs

handle :: forall ieffs fs a .
  ( Rercompose fs )
  => Handler ieffs '[] fs
  -> Prog ieffs a -> RComposes fs a
handle (Handler h) p = handle' h p


handle' :: forall ieffs t fs a .
  ( Monad (t Identity)
  , Rercompose fs )
  => Handler' ieffs '[] t fs
  -> Prog ieffs a -> RComposes fs a
handle' (Handler' run malg)
  = runIdentity
  . fmap @Identity (rercompose @fs @a)
  . run @Identity (absurdEffs . injs)
  . eval (malg (absurdEffs . injs))

-- handleWith :: forall ieffs oeffs xeffs m fs a .
--   ( Monad m
--   , Rercompose fs
--   , Append ieffs (xeffs :\\ ieffs)
--   , Injects oeffs xeffs
--   , Injects (xeffs :\\ ieffs) xeffs
--   )
--   => (forall x. Effs xeffs m x -> m x)
--   -> Handler ieffs oeffs fs
--   -> Prog (ieffs `Union` xeffs) a -> m (RComposes fs a)
-- handleWith xalg (Handler (Handler' run malg))
--   = fmap @m (rercompose @fs @a)
--   . run @m (xalg . injs)
--   . eval (hunion @ieffs @xeffs (malg (xalg . injs)) (mfwd xalg))

-- weaken
--   :: forall ieffs ieffs' oeffs oeffs' fs
--   . ( Injects ieffs ieffs'
--     , Injects oeffs oeffs'
--     )
--   => Handler ieffs' oeffs fs
--   -> Handler ieffs oeffs' fs
-- weaken (Handler (Handler' run malg))
--   = Handler (Handler' (\oalg -> run (oalg . injs)) (\oalg -> malg (oalg . injs) . injs))

-- hide
--   :: forall sigs effs oeffs fs
--   .  (Injects (effs :\\ sigs) effs, Injects oeffs oeffs)
--   => Handler effs oeffs fs -> Handler (effs :\\ sigs) oeffs fs
-- hide h = weaken h

weakenAlg
  :: forall eff eff' m x . (Injects eff eff')
  => (Effs eff' m x -> m x)
  -> (Effs eff  m x -> m x)
weakenAlg alg = alg . injs



class (HFunctor sig, HFunctor (Effs sigs)) => Member' sig sigs (n :: Nat) where
  inj' :: SNat n -> sig f a -> Effs sigs f a
  prj' :: SNat n -> Effs sigs f a -> Maybe (sig f a)


instance (HFunctor sig, (sigs' ~ (sig ': sigs))) => Member' sig sigs' Z where
  inj' :: (HFunctor sig, sigs' ~ (sig : sigs)) => SNat Z -> sig f a -> Effs sigs' f a
  inj' _ = Eff

  prj' :: (HFunctor sig, sigs' ~ (sig : sigs)) => SNat Z -> Effs sigs' f a -> Maybe (sig f a)
  prj' _ (Eff x) = Just x
  prj' _ _        = Nothing

instance (sigs' ~ (sig' ': sigs), HFunctor sig, Member' sig sigs n) => Member' sig sigs' (S n) where
  inj' _ = Effs . inj' (SNat :: SNat n)

  prj' _ (Eff _)  = Nothing
  prj' _ (Effs x) = prj' (SNat :: SNat n) x

type Member :: Effect -> [Effect] -> Constraint
class (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj :: sig f a -> Effs sigs f a
  prj :: Effs sigs m a -> Maybe (sig m a)

instance (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj = inj' (SNat :: SNat (ElemIndex sig sigs))
  prj = prj' (SNat :: SNat (ElemIndex sig sigs))

type family Members (xs :: [Effect]) (xys :: [Effect]) :: Constraint where
  Members '[] xys       = ()
  Members (x ': xs) xys = (Member x xys, Members xs xys, Injects (x ': xs) xys)


-- Injects xs ys means that all of xs is in xys
-- Some other effects may be in xys, so xs <= ys
type  Injects :: [Effect] -> [Effect] -> Constraint
class Injects xs xys where
  injs :: Effs xs f a -> Effs xys f a

instance Injects '[] xys where
  injs :: Effs '[] f a -> Effs xys f a
  injs = absurdEffs
instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

hunion :: forall xs ys f a b
  . ( Append xs (ys :\\ xs)
  ,   Injects (ys :\\ xs) ys )
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs `Union` ys) f a -> b)
hunion xalg yalg = heither @xs @(ys :\\ xs) xalg (yalg . injs)