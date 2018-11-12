{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

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

-- * Coproducts

data (f :+: g) a = L (f a) | R (g a)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (L x) = L (fmap f x)
  fmap f (R y) = R (fmap f y)

-- * Algebras

class Functor f => Alg f a where
  alg :: f a -> a

eval :: Alg f b => (a -> b) -> Free f a -> b
eval gen (Var x) = gen x
eval gen (Op op) = alg (fmap (eval gen) op)

-- | Algebra of coproduct functors
instance (Alg f a, Alg g a) => Alg (f :+: g) a where
  alg (L x) = alg x
  alg (R y) = alg y
