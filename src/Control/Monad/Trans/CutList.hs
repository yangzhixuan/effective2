{-|
Module      : Control.Monad.Trans.CutList
Description : CutList monad transformer
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

module Control.Monad.Trans.CutList where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class

-- | The cutlist transformer, with similar semantics to @ListT@ "done right",
-- but with a @cut@ operation from logic programming.
newtype CutListT m a = CutListT { runCutListT :: m (CutListT' m a) }
  deriving Functor

-- | Internal functor offering cosntructors for t`CutListT`
data CutListT' m a = a :<< (m (CutListT' m a)) | NilT | ZeroT
  deriving Functor

-- | Extracts a list from a t`CutListT` in the context @m@.
fromCutListT :: Monad m => CutListT m a -> m [a]
fromCutListT (CutListT mxs) =
  do xs <- mxs
     case xs of
       x :<< mys -> (x :) <$> fromCutListT (CutListT mys)
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