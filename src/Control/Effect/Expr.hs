{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}

module Control.Effect.Expr where
import Control.Effect

data Add k = Add k k deriving (Functor, Show)
data Sub k = Sub k k deriving (Functor, Show)
data Mul k = Mul k k deriving (Functor, Show)
data Neg k = Neg k   deriving (Functor, Show)
data Abs k = Abs k   deriving (Functor, Show)
data Sig k = Sig k   deriving (Functor, Show)

type Expr = Add :+: Sub :+: Mul :+: Neg :+: Abs :+: Sig

instance Num a => Num (Free Expr a) where
  x + y    = op (Add x y)
  x - y    = op (Sub x y)
  x * y    = op (Mul x y)
  negate x = op (Neg x)
  abs x    = op (Abs x)
  signum x = op (Sig x)
  fromInteger x = var (fromInteger x)

instance Num a => Alg Add a where
  alg (Add x y) = x + y
instance Num a => Alg Sub a where
  alg (Sub x y) = x - y
instance Num a => Alg Mul a where
  alg (Mul x y) = x * y
instance Num a => Alg Neg a where
  alg (Neg x)   = negate x
instance Num a => Alg Abs a where
  alg (Abs x)   = abs x
instance Num a => Alg Sig a where
  alg (Sig x)   = signum x
