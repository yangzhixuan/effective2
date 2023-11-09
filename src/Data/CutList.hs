module Data.CutList where

import Control.Applicative ( Alternative((<|>), empty) )
import Control.Monad ( ap, liftM )
import Control.Monad.Trans.Class ( MonadTrans(..) )

data CutList a = a :< CutList a | Nil | Zero
  deriving Functor

toCutList :: [a] -> CutList a
toCutList (x : xs) = x :< toCutList xs
toCutList []       = Nil

fromCutList :: CutList a -> [a]
fromCutList (x :< xs) = x : fromCutList xs
fromCutList _         = []

instance Semigroup (CutList a) where
  Zero      <> ys = Zero
  Nil       <> ys = ys
  (x :< xs) <> ys = x :< (xs <> ys)

instance Monoid (CutList a) where
  mempty = Nil

instance Applicative CutList where
  pure x = x :< Nil
  (<*>)  = ap

instance Monad CutList where
  m >>= f = join (fmap f m) where
    join :: CutList (CutList a) -> CutList a
    join ((a :< xs) :< xss) = a :< join (xs :< xss)
    join (Nil  :< xss) = join xss
    join (Zero :< _)   = Zero
    join Nil           = Nil
    join Zero          = Zero

instance Alternative CutList where
  empty            = Nil
  Zero      <|> ys = Nil
  Nil       <|> ys = ys
  (x :< xs) <|> ys = x :< (xs <|> ys)

data CutListT' m a = a :<< (m (CutListT' m a)) | NilT | ZeroT
  deriving Functor

newtype CutListT m a = CutListT { runCutListT :: m (CutListT' m a) }
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
  CutListT m <|> CutListT n = CutListT $ m >>= aux
   where
    aux (a :<< k) = return $ a :<< (k >>= aux)
    aux NilT        = n
    aux ZeroT       = return ZeroT -- aux ZeroT       = return NilT

instance Monad m => Monad (CutListT m) where
  CutListT m >>= f = CutListT $ m >>= \x -> case x of
    a :<< m -> runCutListT $ f a <|> (CutListT m >>= f)
    NilT    -> return NilT
    ZeroT   -> return ZeroT

instance MonadTrans CutListT where
  lift :: Monad m => m a -> CutListT m a
  lift m = CutListT $ liftM (\a -> a :<< return NilT) m
