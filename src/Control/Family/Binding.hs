module Control.Family.Binding where

import Data.Nat.Kind

newtype VarBinding (n :: Nat) (f :: Type -> Type) (x :: Type)
  = VarBinding (f (Iterate n Maybe x))
