{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Effect where

data Free f a
  = Var a
  | Op (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Var x) = Var (f x)
  fmap f (Op op) = Op (fmap (fmap f) op)

instance Functor f => Applicative (Free f) where
  pure = Var
  Var f <*> x = fmap f x
  Op op <*> x = Op (fmap (<*> x) op)

instance Functor f => Monad (Free f) where
  Var x >>= k = k x
  Op op >>= k = Op (fmap (>>= k) op)

class Functor f => Alg f a where
  alg :: f a -> a

eval :: Alg f b => (a -> b) -> Free f a -> b
eval gen (Var x) = gen x
eval gen (Op op) = alg (fmap (eval gen) op)

