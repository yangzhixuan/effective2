module Control.Effect.Alternative.Type where

import Control.Family.Algebraic
import Control.Family.Scoped

data Empty' a where
  Empty :: Empty' a
  deriving Functor
type Empty = Alg Empty'

type Choose = Scp Choose'
data Choose' a where
  Choose :: a -> a -> Choose' a
  deriving Functor