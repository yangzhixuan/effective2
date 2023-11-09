{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Cut where

import Control.Effect
import Control.Effect.Nondet ( Once(..), Or(..), Stop(..) )

import Data.CutList ( CutListT(..), CutListT'(..), fromCutListT' )
import Data.HFunctor ( HFunctor(..) )
import Data.HFunctor.HComposes ( HComposes )
import Control.Applicative ( Alternative((<|>), empty) )
import Control.Monad ( join, ap, liftM, replicateM)
import Control.Monad.Trans.Class (lift)

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

data CutFail a where
  CutFail :: CutFail a
  deriving Functor


cut :: (Members [Or, Stop, CutFail] sig) => Prog sig ()
cut = skip <|> cutFail

cutFail :: Member CutFail sig => Prog sig a
cutFail = injCall (Alg CutFail)

data CutCall a where
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

onceNondet :: Handler [Once, Stop, Or, CutFail, CutCall] '[CutListT] '[[]] '[]
onceNondet = fuse @'[CutCall, CutFail, Or] @'[] onceCut cutList
