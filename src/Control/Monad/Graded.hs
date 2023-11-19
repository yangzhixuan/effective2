{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Monad.Graded (GradedMonad(..)) where

import Data.Kind (Type, Constraint)

class GradedMonad (m :: k -> Type -> Type) where
  type Unit m :: k
  type Plus m (i :: k) (j :: k) :: k
  type Inv  m (i :: k) (j :: k) :: Constraint

  (>>=) :: Inv m i j => m i a -> (a -> m j b) -> m (Plus m i j) b
  return :: a -> m (Unit m) a
