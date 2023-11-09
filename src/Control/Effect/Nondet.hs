{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet where

import Prelude hiding (or)

import Data.HFunctor ( HFunctor(..) )
import Data.List.Kind ( type (:++) )

import Control.Effect
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad ( join, ap, liftM, replicateM)
import Control.Monad.Trans.Class ( MonadTrans(..) )
import Control.Arrow ( Arrow(second) )


data Stop a where
  Stop :: Stop a
  deriving Functor

stop :: forall sig a . Member Stop sig => Prog sig a
stop  = injCall (Alg Stop)

data Or a where
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


-------------------------------
-- Example: Backtracking (and Culling?)
data Once a where
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
