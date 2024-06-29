{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Cut where

import Control.Effect
import Control.Effect.Nondet
import Prelude hiding (or)

import Control.Family.Algebraic
import Control.Family.Scoped

import Data.CutList ( CutListT(..), CutListT'(..), fromCutListT' )
import Data.HFunctor ( HFunctor(..) )
import Control.Applicative ( Alternative((<|>), empty) )

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

type CutFail = Alg CutFail'
data CutFail' a where
  CutFail :: CutFail' a
  deriving Functor

cutFail :: Member CutFail sig => Prog sig a
cutFail = injCall (Alg CutFail)

type CutCall = Scp CutCall'
data CutCall' a where
  CutCall :: a -> CutCall' a
  deriving Functor

cut :: (Members [Or, CutFail] sig) => Prog sig ()
cut = or skip cutFail

cutCall :: Member CutCall sig => Prog sig a -> Prog sig a
cutCall p = cutCall' progAlg p -- injCall (Scp (CutCall (fmap return p)))

cutCall' :: (Monad m, Member CutCall sig)
  => (forall a . Effs sig m a -> m a) -> m a -> m a
cutCall' alg p = (alg . inj) (Scp (CutCall p))

skip :: Monad m => m ()
skip = return ()

callAlg :: Monad m => CutListT m a -> CutListT m a
callAlg (CutListT mxs) = CutListT $
  do xs <- mxs
     case xs of
       x :<< mys -> return (x :<< runCutListT (callAlg (CutListT mys)))
       NilT      -> return NilT
       ZeroT     -> return NilT   -- clear the cut flag at the boundary of call

cutListAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> forall x. Effs [Stop, Or, CutFail, CutCall] (CutListT m) x -> CutListT m x
cutListAlg oalg op
  | Just (Alg Stop)        <- prj op = empty
  | Just (Alg (Or x y))    <- prj op = return x <|> return y
  | Just (Alg CutFail)     <- prj op = CutListT (return ZeroT)
  | Just (Scp (CutCall x)) <- prj op = callAlg x

-- cutList :: Handler [Stop, Or, CutFail, CutCall] '[] '[[]]
-- cutList = handler fromCutListT' cutListAlg

cutList' :: Handler [Stop, Or, CutFail, CutCall] '[] '[CutListT] '[[]]
cutList' = handler' fromCutListT' cutListAlg


instance HFunctor CutListT where
  hmap :: (Functor f, Functor g) =>
    (forall x. f x -> g x) -> CutListT f a -> CutListT g a
  hmap h (CutListT x) = CutListT (fmap (hmap h) (h x))

instance HFunctor CutListT' where
  hmap _ ZeroT      = ZeroT
  hmap _ NilT       = NilT
  hmap h (x :<< xs) = x :<< fmap (hmap h) (h xs)

onceCut' :: Handler '[Once] '[CutCall, CutFail, Or] '[] '[]
onceCut' = interpretM onceCutAlg

onceCutAlg :: forall oeff m . (Monad m , Members [CutCall, CutFail, Or] oeff)
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs '[Once] m x -> m x)
onceCutAlg oalg op
  | Just (Scp (Once p)) <- prj op
  = cutCall' oalg (do x <- p
                      eval oalg (do cut
                                    return x))

onceNondet' :: Handler '[Once, Stop, Or, CutFail, CutCall] '[] ('[CutListT]) '[[]]
onceNondet' = fuse onceCut' cutList'

