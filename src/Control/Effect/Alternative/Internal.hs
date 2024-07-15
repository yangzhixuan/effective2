module Control.Effect.Alternative.Internal where

import Control.Family.Algebraic

data Empty' a where
  Empty :: Empty' a
  deriving Functor
type Empty = Alg Empty'

type Choose = Alg Choose'
data Choose' a where
  Choose :: a -> a -> Choose' a
  deriving Functor