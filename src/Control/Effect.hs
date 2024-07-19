{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ImplicitParams #-}

module Control.Effect
  ( module Control.Effect.Type
  , Prog(..)
  , Progs
  , Member(..)
  , Members(..)
  , Handler (..)
  , Injects (..)
  , handler
  , handlerT
  , call
  , progAlg
  , interpret
  , interpretM
  , handle
  , handle'
  , handle''
  , handleM
  , eval
  , fuse, (|>)
  , pipe, (||>)
  , hide
  , joinAlg
  , (#)
  , identity
  , weakenProg
  ) where


import Control.Effect.Type
import Control.Effect.Alternative.Type
import Control.Applicative

import Control.Family.Algebraic
import Control.Family.Scoped

import Data.Kind ( Type )
import Data.List.Kind
import Data.Functor.Identity
import Data.Functor.Composes
import Data.HFunctor
import Data.HFunctor.HComposes
import Control.Family

import Control.Monad ( join, (>=>))

{-# INLINE joinAlg #-}
joinAlg :: forall sig1 sig2 oeff t m .
  ( Monad m, KnownNat (Length sig1) )
  => ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig1 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig2 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs (sig1 :++ sig2) (t m) x -> t m x))
joinAlg falg galg oalg =
  heither @sig1 @sig2 (falg oalg) (galg oalg)

{-# INLINE (#) #-}
(#) :: forall sig1 sig2 m .
  (Monad m, KnownNat (Length sig1))
  => (Algebra sig1 m)
  -> (Algebra sig2 m)
  -> (Algebra (sig1 :++ sig2) m)
falg # galg = heither @sig1 @sig2 (falg) (galg)


---------------------------------------
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
  Return f        <*> p         = fmap f p
--   p               <*> Return x  = fmap ($ x) p
  Call opf hkf kf <*> q         = Call opf hkf ((<*> q) . kf)

  {-# INLINE (*>) #-}
  (*>) :: Prog effs a -> Prog effs b -> Prog effs b
  (*>) = liftA2 (const id)

  {-# INLINE (<*) #-}
  (<*) :: Prog effs a -> Prog effs b -> Prog effs a
  (<*) = liftA2 const

  {-# INLINE liftA2 #-}
  liftA2 :: (a -> b -> c) -> Prog effs a -> Prog effs b -> Prog effs c
  liftA2 f (Return x) q        = fmap (f x) q
--   liftA2 f p (Return y)        = fmap (flip f y) p
  liftA2 f (Call opx hkx kx) q = Call opx hkx ((flip (liftA2 f) q) . kx)

instance (Member Choose sigs, Member Empty sigs)
  => Alternative (Prog sigs) where
  {-# INLINE empty #-}
  empty = call (Alg Empty)

  {-# INLINE (<|>) #-}
  xs <|> ys = call (Scp (Choose (fmap return xs) (fmap return ys)))

instance Monad (Prog effs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  Return x >>= f = f x
  Call op hk k  >>= f = Call op hk (k >=> f)

weakenProg :: forall effs effs' a
  .  Injects effs effs'
  => Prog effs a -> Prog effs' a
weakenProg (Return x) = Return x
-- weakenProg (Call op)   =
--     Call ( injs @effs @effs'
--          . hmap (weakenProg @effs @effs')
--          . fmap (weakenProg @effs @effs')
--          $ op )
weakenProg (Call op hk k)   =
    Call (injs op) (weakenProg @effs @effs' . hk) (weakenProg @effs @effs' . k)

-- Universal property from initial monad `Prog sig a` equipped with
-- `sig m -> m`
eval :: Monad m
  => Algebra effs m
  -> Prog effs a -> m a
eval halg (Return x) = return x
-- eval halg (Call op)  =
  -- join (halg ((fmap (eval halg)
--              . hmap (eval halg)) op))
eval halg (Call op hk k)  =
    -- join . halg . fmap (eval halg . k) . hmap (eval halg . hk) $ op
    join . halg . fmap (eval halg . k) . hmap (eval halg . hk) $ op

-- join (halg (eval halg . hk) (eval halgl . k) op)
--   join (halg ((fmap (eval halg) . hmap (eval halg)) op))

-- Universal property from the GADT, Functorial Algebra
fold :: forall f effs a . Functor f
  => (forall x . (Effs effs f) (f x) -> f x)
  -> (forall x . x -> f x)
  -> Prog effs a -> f a
fold falg gen (Return x) = gen x
-- fold falg gen (Call op)  =
--   falg ((fmap (fold falg gen) . hmap (fold falg gen)) op)
fold falg gen (Call op hk k) =
  falg ((fmap (fold falg gen . k) . hmap (fold falg gen . hk)) op)

{-# INLINE call #-}
call :: forall sub sup a . (Member sub sup, HFunctor sub) => sub (Prog sup) (Prog sup a) -> Prog sup a
-- call x = Call (inj x)
call x = Call (inj x) id id

{-# INLINE prjCall #-}
prjCall :: forall sub sup a . Member sub sup => Prog sup a -> Maybe (sub (Prog sup) (Prog sup a))
-- prjCall (Call op) = prj op
prjCall (Call op hk k) = prj (hmap hk . fmap k $ op)
prjCall _              = Nothing

progAlg :: Effs sig (Prog sig) a -> Prog sig a
-- progAlg = Call . fmap return
progAlg x = Call x id return

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
  data Handler effs oeffs t fs feffs
```
where `feffs` is the family of effects that can be forwarded, and then we would
need constraints such as `Forward feffs t` to be in place. The advantage
is that custom effects can forward more flexibly, but at the cost
of added complexity in the signature.
That complexity could be hidden by another datatype, much
in the same way as `Handler` obscures the underlying `t` type.

Another design, which was previously implemented
is to have families explicit in the handler signature.
A list of such families would indicate those that can be handled.
If `h1 :: Handler eff1 t1 fam1`, and `h2 :: Handler eff2 t2 fam2`, then the two
can be composed so long as `fam1 ⊇ fam2`. All of `eff1` will be
dealt with into carrier the `t1` carrier, and need not concern `h2`,
so long as the carrier is compatible with `eff2`. However, if `eff2` contains a
family of effects that is not recognised by `h1`, then it is
impossible to forward those effects and fusion is impossible.

Yet another design is to use a handler of the form:
```
type Handler
  :: [Effect]                          -- effs  : input effects
  -> [Effect]                          -- oeffs : output effects
  -> [Type -> Type]                    -- f     : carrier type
  -> Type
data Handler effs oeffs fs
  =  forall t . (MonadTrans t
              -- Forward effs t
                )
  => Handler (Handler effs oeffs t fs)
```
This is a wrapper around a handler that involves a transformer
held as an existential held in some unexposed variable `t`.
The problem with this a approach is that handlers can no longer
fuse easily, since fusion requires a `Forward` constraint
that mentions `t` explicitly.

The closest `fuse` using this interface is:
```
fuse
  :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 oeffs1' .
  ( Functor (RComps fs1), RSplit fs2
  , Append effs1 (effs2 :\\ effs1),  Append (oeffs1 :\\ effs2) effs2
  , Injects oeffs2 ((oeffs1 :\\ effs2) :++ (oeffs2 :\\ (oeffs1 :\\ effs2)))
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (oeffs1 :\\ effs2)    ((oeffs1 :\\ effs2) :++ (oeffs2 :\\ (oeffs1 :\\ effs2)))
  , Injects (effs2 :\\ effs1) effs2
  , oeffs1' ~ oeffs1 :\\ effs2
  , forall t . MonadTrans t => Forward effs2 t
  , forall t . MonadTrans t => Forward oeffs1' t
  )
  => Handler effs1 oeffs1 fs2
  -> Handler effs2 oeffs2 fs1
  -> Handler (effs1 :++ (effs2 :\\ effs1))
             ((oeffs1 :\\ effs2) :++ (oeffs2 :\\ (oeffs1 :\\ effs2)))
             (fs2 :++ fs1)
fuse (Handler h1) (Handler h2) = Handler (fuse h1 h2)
```
This uses `Forward` constraints that work regardless of `t`,
that is, `forall t . MonadTrans t => Forward effs2 t`. While this is definable
for algebraic effects, it is not possible for all scoped effects.

-}

type Handler
  :: [Effect]                             -- effs  : input effects
  -> [Effect]                             -- oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ts    : monad transformer
  -> [Type -> Type]                       -- fs    : carrier type
  -> Type
data Handler effs oeffs ts fs =
  Handler
  { run  :: forall m . Monad m
         => Algebra oeffs m
         -> (forall x . HComps ts m x -> m (RComps fs x))

  , malg :: forall m . Monad m
         => Algebra oeffs m
         -> Algebra effs (HComps ts m)
  }

-- The definition of `handler` motivates the need for a snoc list
-- in the functor carrier. Without this, we need to expose the functors
-- using `Exposes fs '[f']`, and this becomes very burdensome for the
-- end user.
handler
  :: (Functors fs, forall f . Functor f => Functor (t f))
  => (forall m a . Monad m => t m a -> m (RComposes fs a))
  -> (forall m . Monad m => Algebra oeffs m -> Algebra effs (t m))
  -> Handler effs oeffs '[t] fs
handler run malg = Handler
  (\oalg -> fmap dercompose  . unHNil . run . unHCons)
  (\oalg -> HCons . malg (HNil . oalg . hmap unHNil) . hmap unHCons)

-- TODO:
-- The following is a more general handler type that generalises `handler`
-- and would be easier to use than `handlerT`.
-- However, it has an illegal type because a type synonym family
-- appears in the instance: `Functor (HComposes ts m)` is not allowed.
-- We need it because of the `hmap` in the definition of `alg'`, since
-- an `HFunctor` requires both of its parameters to be functors. It's possible
-- that with some careful class redefinitions that this might be implementable.
--
-- handler'
--   :: forall effs oeffs ts fs.
--      (Functors fs, forall m . HRecompose ts m, forall m . Functor m => Functor (HComposes ts m))
--   => (forall m a . Monad m => HComposes ts m a -> m (RComposes fs a))
--   -> (forall m . Monad m => Algebra oeffs m -> Algebra effs (HComposes ts m))
--   -> Handler effs oeffs ts fs
-- handler' run alg = Handler run' alg' where
--   run' :: Monad m => Algebra oeffs m -> forall x. HComps ts m x -> m (RComps fs x)
--   run' oalg = fmap dercompose . run . hrecompose
--
--   alg' :: Monad m => Algebra oeffs m -> Algebra effs (HComps ts m)
--   alg' oalg = hdecompose . alg oalg . hmap hrecompose

handlerT
  :: forall effs oeffs ts fs
  .  (Functors fs)
  => (forall m a . Monad m => HComps ts m a -> m (RComposes fs a))
  -> (forall m . Monad m => Algebra oeffs m -> Algebra effs (HComps ts m))
  -> Handler effs oeffs ts fs
handlerT run malg = Handler (const (fmap dercompose . run)) malg

identity :: Handler '[] '[] '[] '[]
identity = Handler run malg where

  run :: Functor m => Algebra '[] m -> (forall x. HComps '[] m x -> m (RComps '[] x))
  run _ (HNil x) = fmap RCNil x

  malg :: Algebra '[] m -> Algebra '[] (HComps '[] m)
  malg _ = absurdEffs

weaken
  :: forall effs effs' oeffs oeffs' ts fs
  . ( Injects effs effs'
    , Injects oeffs oeffs'
    )
  => Handler effs' oeffs ts fs
  -> Handler effs oeffs' ts fs
weaken (Handler run malg)
  = (Handler (\oalg -> run (oalg . injs)) (\oalg -> malg (oalg . injs) . injs))

hide
  :: forall sigs effs oeffs ts fs
  .  (Injects (effs :\\ sigs) effs, Injects oeffs oeffs)
  => Handler effs oeffs ts fs
  -> Handler (effs :\\ sigs) oeffs ts fs
hide h = weaken h

type AlgebraT effs oeffs t = forall m.  Monad m
  => (forall x. Effs oeffs m x -> m x)
  -> (forall x. Effs effs (t m) x -> t m x)

interpret
  :: forall effs oeffs
  .  (forall m x . Effs effs m x -> Prog oeffs x)
  -> Handler effs oeffs '[] '[]
interpret alg = interpretM talg
  where
    talg :: forall m . Monad m
         => (forall x. Effs oeffs m x -> m x)
         -> (forall x. Effs effs m x  -> m x)
    talg oalg op = eval oalg (alg op)

interpretM
  :: forall effs oeffs .
    (forall m . Monad m =>
      (forall x . Effs oeffs m x -> m x) -> (forall x . Effs effs m x -> m x))
  -> Handler effs oeffs '[] '[]
interpretM alg
  = Handler @effs @oeffs @'[]
      (const (\(HNil mx) -> fmap RCNil mx))
      (\oalg -> HNil . alg oalg . hmap unHNil)

interpretT
  :: Handler effs oeffs ts '[]
interpretT = Handler run malg where
  run :: Monad m => Algebra oeffs m -> forall x. HComps ts m x -> m (RComps '[] x)
  run = undefined

  malg :: Monad m => Algebra oeffs m -> Algebra effs (HComps ts m)
  malg = undefined

{-

Fusing handlers `h1 :: Handler effs1 oeffs1 t1 fs1` and `h2 :: Handler effs2
oeffs2 t2 fs2` results in a handler that can deal with the effects of `eff1` and
those of `eff2`, as well as appropriately deal with effects `oeff1` that get
output by the first handler.

A handler consists of `malg`, which deals with all the operations in the
syntax tree that the handler will be applied to, and `run`, which
turns the final transformed monad into a functor.

The task of of the `malg` algebra is to interpret the union of `effs1` and
`effs2`. To do so, it must appropriately use the output algebra `oalg` that it
is given, which is responsible for handling any effects that the handler
may produce. The effects in `oeffs1` are produced by `h1`, and
the effects in `oeffs2` are produced by `h2`. If an effect `oeff1` is in
`effs2`, then it means that it is produced by `h1` and can be consumed by `h2`.
To do so, `malg2` is used. Any other effect produced by `h1` will not
be recognised by `h2`, and must therefore be forwarded into the `t2`
transformer as outlined by the `fwd @(oeffs1 :\\ effs2) t2` function.

Effects

means that any syntax of `eff2` must be forwarded by the
transformer `t1` of `h1`, since the effect must bypass `eff1` into syntax in the
context given by `t1`, ready to be consumed by the second handler.  This is
captured by the `Forward eff2 t1` constraint.

When the effect is from `effs2`, the `malg2` handler must
of course play a part. The problem is that the
carrier that is targeted is `t ~ HCompose t1 t2`,
whereas `malg` can only work for `t2` carriers.
This makes sense, since the operations in `effs2` must operate
only after `h1` has done its work on the syntax tree.
To make use of `malg` operate with the `t1` carrier,
-}
fuse, (|>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 effs oeffs ts fs
  . ( effs  ~ effs1 `Union` effs2
    , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
    , ts    ~ ts1 :++ ts2
    , fs    ~ fs1 :++ fs2
    , Functor (RComps fs2)
    , forall m . Monad m => Monad (HComps ts2 m)
    , RSplit fs1
    , Forwards (oeffs1 :\\ effs2) (ts2)
    , Forwards effs2 (ts1)
    , Injects (oeffs1 :\\ effs2) oeffs
    , Injects (effs2 :\\ effs1) effs2
    , Injects oeffs2 oeffs
    , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
    , HExpose ts1
    , KnownNat (Length (oeffs1 :\\ effs2))
    , KnownNat (Length (effs1))
    )
  => Handler effs1 oeffs1 ts1 fs1
  -> Handler effs2 oeffs2 ts2 fs2
  -> Handler effs  oeffs  ts  fs
(|>) = fuse
fuse (Handler run1 malg1)  (Handler run2 malg2) = Handler run malg where
  run :: forall m . Monad m => Algebra oeffs m -> forall x. HComps ts m x -> m (RComps fs x)
  run oalg
    = fmap unrsplit
    . run2 (oalg . injs)
    . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
        (fwds @(oeffs1 :\\ effs2) @(ts2) (weakenAlg oalg))
        (malg2 (weakenAlg oalg)))
    . hexpose @ts1

  malg :: forall m . Monad m => Algebra oeffs m -> Algebra effs (HComps ts m)
  malg oalg
    = hunexpose @ts1
    . hunion @effs1 @effs2
        (malg1 (weakenAlg $
          heither @(oeffs1 :\\ effs2) @effs2
            (fwds @(oeffs1 :\\ effs2) @ts2 (weakenAlg oalg))
            (malg2 (weakenAlg oalg))))
        (fwds @effs2 @ts1 (malg2 (oalg . injs)))
    . hmap (hexpose @ts1)

pipe, (||>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 effs oeffs ts fs
  . ( effs  ~ effs1
    , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
    , ts    ~ ts1 :++ ts2
    , fs    ~ fs1 :++ fs2
    , Functor (RComps fs2)
    , RSplit fs1
    , Forwards (oeffs1 :\\ effs2) ts2
    , Forwards effs2 ts1
    , Injects (oeffs1 :\\ effs2) oeffs
    , Injects (effs2 :\\ effs1) effs2
    , Injects oeffs2 oeffs
    , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
    , forall m . Monad m => Monad (HComps ts2 m)
    , HExposes ts1 ts2
    , KnownNat (Length (oeffs1 :\\ effs2))
    )
  => Handler effs1 oeffs1 ts1 fs1
  -> Handler effs2 oeffs2 ts2 fs2
  -> Handler effs  oeffs  ts  fs
(||>) = pipe
pipe (Handler run1 malg1)  (Handler run2 malg2) = Handler run malg where
  run :: forall m . Monad m => Algebra oeffs m -> forall x. HComps ts m x -> m (RComps fs x)
  run oalg x
    = fmap unrsplit
    . run2 (oalg . injs)
    . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
        (fwds @(oeffs1 :\\ effs2) @ts2 (weakenAlg oalg))
        (malg2 (weakenAlg oalg)))
    . hexposes @ts1 @ts2 $ x

  malg :: forall m . Monad m =>
    Algebra oeffs m ->
    Algebra effs (HComps ts m)
  malg oalg
    = hunexposes @ts1 @ts2
    . malg1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
        (fwds @(oeffs1 :\\ effs2) @ts2 (weakenAlg oalg))
        (malg2 (weakenAlg oalg)))
    . hmap (hexposes @ts1 @ts2)

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


handle :: forall effs ts fs a .
  ( Monad (HComps ts Identity)
  , Functors fs )
  => Handler effs '[] ts fs
  -> Prog effs a -> RComposes fs a
handle (Handler run malg)
  = rercompose @fs @a
  . runIdentity
  . run @Identity (absurdEffs . injs)
  . eval (malg (absurdEffs . injs))

handle'
  :: forall effs oeffs ts fs a . (Monad (HComps ts (Prog oeffs)), Functors fs)
  => Handler effs oeffs ts fs -> Prog effs a -> Prog oeffs (RComposes fs a)
handle' (Handler run malg)
  = fmap rercompose . run (\x -> Call x id return) . eval (malg (\x -> Call x id return))

handle''
  :: forall sig eff oeffs ts fs a
  .  (Injects oeffs (oeffs :++ sig), Injects sig (oeffs :++ sig)
  ,  Monad (HComps ts (Prog (oeffs :++ sig)))
  , Functors fs
  , KnownNat (Length eff)
  , Forward (Effs sig)  (HComps ts)
  )
  => Handler eff oeffs ts fs -> Prog (eff :++ sig) a -> Prog (oeffs :++ sig) (RComposes fs a)
handle'' (Handler run malg)
  = fmap rercompose
  . run (\x -> Call (injs x) id return)
  . eval (heither @eff @sig (malg @(Prog (oeffs :++ sig)) (\x -> Call (injs x) id return))
                            (fwd (\x -> Call (injs x) id return)))


handleM :: forall effs oeffs xeffs m ts fs a .
  ( Monad m
  , forall m . Monad m => Monad (HComps ts m)
  , Functors fs
  , Forwards xeffs ts
  , Injects oeffs xeffs
  , Injects (xeffs :\\ effs) xeffs
  , KnownNat (Length (effs))
  )
  => Algebra xeffs m
  -> Handler effs oeffs ts fs
  -> Prog (effs `Union` xeffs) a -> m (RComposes fs a)
handleM xalg (Handler run malg)
  = fmap @m (rercompose @fs @a)
  . run @m (xalg . injs)
  . eval (hunion @effs @xeffs (malg (xalg . injs)) (fwds xalg))