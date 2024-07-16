{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Data.CutList where

import Control.Applicative ( Alternative((<|>), empty) )
import Control.Monad ( ap, liftM )
import Control.Monad.Trans.Class ( MonadTrans(..) )
import Control.Family
import Control.Family.Scoped

data CutList a = a :< CutList a | Nil | Zero
  deriving Functor

toCutList :: [a] -> CutList a
toCutList (x : xs) = x :< toCutList xs
toCutList []       = Nil

fromCutList :: CutList a -> [a]
fromCutList (x :< xs) = x : fromCutList xs
fromCutList _         = []

instance Semigroup (CutList a) where
  Zero      <> _  = Zero
  Nil       <> ys = ys
  (x :< xs) <> ys = x :< (xs <> ys)

instance Monoid (CutList a) where
  mempty = Nil

instance Applicative CutList where
  pure x = x :< Nil
  (<*>)  = ap

instance Monad CutList where
  mx >>= f = join (fmap f mx) where
    join :: CutList (CutList a) -> CutList a
    join ((x :< xs) :< xss) = x :< join (xs :< xss)
    join (Nil  :< xss) = join xss
    join (Zero :< _)   = Zero
    join Nil           = Nil
    join Zero          = Zero

instance Alternative CutList where
  empty            = Nil
  Zero      <|> _  = Nil
  Nil       <|> ys = ys
  (x :< xs) <|> ys = x :< (xs <|> ys)

newtype CutListT m a = CutListT { runCutListT :: m (CutListT' m a) }
  deriving Functor

data CutListT' m a = a :<< (m (CutListT' m a)) | NilT | ZeroT
  deriving Functor

fromCutListT' :: Monad m => CutListT m a -> m [a]
fromCutListT' (CutListT mxs) =
  do xs <- mxs
     case xs of
       x :<< mys -> (x :) <$> fromCutListT' (CutListT mys)
       NilT      -> return []
       ZeroT     -> return []

instance Monad m => Applicative (CutListT m) where
  pure x = CutListT (return (x :<< return NilT))
  (<*>) = ap

instance Monad m => Alternative (CutListT m) where
  empty = CutListT $ return NilT
  CutListT mxs <|> CutListT mys = CutListT $ mxs >>= k
   where
    k (x :<< mxs') = return $ x :<< (mxs' >>= k)
    k NilT         = mys
    k ZeroT        = return ZeroT -- k ZeroT = return NilT

instance Monad m => Monad (CutListT m) where
  CutListT mxs >>= k = CutListT $ mxs >>= \xxs -> case xxs of
    x :<< mxs' -> runCutListT $ k x <|> (CutListT mxs' >>= k)
    NilT       -> return NilT
    ZeroT      -> return ZeroT

instance MonadTrans CutListT where
  lift :: Monad m => m a -> CutListT m a
  lift mx = CutListT $ liftM (\x -> x :<< return NilT) mx

instance Functor f => Forward (Scp f) CutListT where
  fwd alg (Scp op) = (CutListT . alg . Scp . fmap runCutListT) op