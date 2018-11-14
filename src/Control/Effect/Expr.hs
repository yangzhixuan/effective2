{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Effect.Expr where
import Control.Effect

data Add k = Add k k deriving (Functor, Show, Foldable)
data Sub k = Sub k k deriving (Functor, Show, Foldable)
data Mul k = Mul k k deriving (Functor, Show, Foldable)
data Neg k = Neg k   deriving (Functor, Show, Foldable)
data Abs k = Abs k   deriving (Functor, Show, Foldable)
data Sig k = Sig k   deriving (Functor, Show, Foldable)

type Expr = Add :+: Sub :+: Mul :+: Neg :+: Abs :+: Sig

instance Num a => Num (Free Expr a) where
  x + y    = op (Add x y)
  x - y    = op (Sub x y)
  x * y    = op (Mul x y)
  negate x = op (Neg x)
  abs x    = op (Abs x)
  signum x = op (Sig x)
  fromInteger x = var (fromInteger x)

deriving instance Num a => Num (Eval a)

instance Num a => Alg Add (Eval a) where
  alg (Add x y) = x + y
instance Num a => Alg Sub (Eval a) where
  alg (Sub x y) = x - y
instance Num a => Alg Mul (Eval a) where
  alg (Mul x y) = x * y
instance Num a => Alg Neg (Eval a) where
  alg (Neg x)   = negate x
instance Num a => Alg Abs (Eval a) where
  alg (Abs x)   = abs x
instance Num a => Alg Sig (Eval a) where
  alg (Sig x)   = signum x


instance Num a => Alg Add (Vars a) where
  alg (Add x y) = x <> y
instance Num a => Alg Sub (Vars a) where
  alg (Sub x y) = x <> y
instance Num a => Alg Mul (Vars a) where
  alg (Mul x y) = x <> y
instance Num a => Alg Neg (Vars a) where
  alg (Neg x)   = x
instance Num a => Alg Abs (Vars a) where
  alg (Abs x)   = x
instance Num a => Alg Sig (Vars a) where
  alg (Sig x)   = x
