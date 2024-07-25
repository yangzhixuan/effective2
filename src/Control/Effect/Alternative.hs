{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Alternative where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped

import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad.Trans.Class

data Empty' a where
  Empty :: Empty' a
  deriving Functor
type Empty = Alg Empty'

type Choose = Scp Choose'
data Choose' a where
  Choose :: a -> a -> Choose' a
  deriving Functor

alternativeAlg
  :: (MonadTrans t, Alternative (t m), Monad m)
  => (Algebra oeffs m)
  -> (Algebra [Empty , Choose] (t m))
alternativeAlg oalg eff
  | (Just (Alg Empty))          <- prj eff = empty
  | (Just (Scp (Choose xs ys))) <- prj eff = xs <|> ys

instance (Member Choose sigs, Member Empty sigs)
  => Alternative (Prog sigs) where
  {-# INLINE empty #-}
  empty = call (Alg Empty)

  {-# INLINE (<|>) #-}
  xs <|> ys = call (Scp (Choose (fmap return xs) (fmap return ys)))
