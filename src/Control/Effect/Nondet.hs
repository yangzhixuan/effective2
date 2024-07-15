{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet
  ( module Control.Effect.Nondet
  , module Control.Effect.Alternative.Internal) where

import Prelude hiding (or)

import Control.Effect.Alternative.Internal
import Control.Effect
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad.Trans.Class ( MonadTrans(..) )
import Control.Monad.Trans.List

import Control.Family.Algebraic
import Control.Family.Scoped

stop :: Members '[Empty] sig => Prog sig a
stop  = injCall (Alg Empty)

or :: Members '[Choose] sig => Prog sig a -> Prog sig a -> Prog sig a
or x y = injCall (Alg (Choose x y))

select :: Members [Choose, Empty] sig => [a] -> Prog sig a
select = foldr (or . return) stop

selects :: [a] -> Progs [Choose, Empty] (a, [a])
selects []      =  empty
selects (x:xs)  =  return (x, xs)  <|>  do  (y, ys) <- selects xs
                                            return (y, x:ys)

alternativeAlg
  :: (MonadTrans t, Alternative (t m), Monad m)
  => (Algebra oeffs m)
  -> (Algebra [Empty , Choose] (t m))
alternativeAlg oalg eff
  | Just (Alg Empty)        <- prj eff = empty
  | Just (Alg (Choose x y)) <- prj eff = return x <|> return y

nondet :: Handler [Empty, Choose] '[] '[ListT] '[[]]
nondet = handler runListT' alternativeAlg

-- This does not work becuase `Choose` is algebraic, for a greedy approach
-- it must favour the lhs, but `return x <|> return y` prevents this
-- greedy :: Handler [Empty, Choose] '[] '[MaybeT] '[Maybe]
-- greedy = handler runMaybeT alternativeAlg

-------------------------------
-- Example: Backtracking (and Culling?)
type Once = Scp Once'
data Once' a where
  Once :: a -> Once' a
  deriving Functor

once
  :: Member Once sig => Prog sig a -> Prog sig a
once p = injCall (Scp (Once (fmap return p)))

-- Everything can be handled together. Here is the non-modular way
-- list :: (Member (Choose) sig, Member (Empty) sig, Member (Once) sig) => Prog sig a -> [a]
list :: Prog [Empty, Choose, Once] a -> [a]
list = eval halg where
  halg :: Effs [Empty, Choose, Once] [] a -> [a]
  halg op
    | Just (Alg Empty)          <- prj op = []
    | Just (Alg (Choose x y))      <- prj op = [x, y]
    | Just (Scp (Once []))     <- prj op = []
    | Just (Scp (Once (x:xs))) <- prj op = [x]

backtrackAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Empty, Choose, Once] (ListT m) x -> ListT m x)
backtrackAlg oalg op
  | Just (Alg Empty)     <- prj op = empty
  | Just (Alg (Choose x y)) <- prj op = return x <|> return y
  | Just (Scp (Once p)) <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))


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
  -> (forall x. Effs [Empty, Choose, Once] (ListT m) x -> ListT m x)
backtrackAlg' = joinAlg alternativeAlg backtrackOnceAlg
-- TODO: The alternative with monad transformers is painful.
-- TODO: this becomes interesting when different search strategies are used

backtrack :: Handler [Empty, Choose, Once] '[] '[ListT] '[[]]
backtrack = handler runListT' backtrackAlg'
