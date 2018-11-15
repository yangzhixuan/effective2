# Effective

The `effective` library is an effect handlers library that is designed
to allow users to define and interpret their own languages and
effects.

## Preamble

Various language extensions are required for the `effective` library:
```haskell
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
```
The `effective` library is imported via `Control.Effect`:
```haskell
import Control.Effect
```

## Introduction

Consider a language that can only perform addition.
```haskell
data Add k = Add k k deriving (Show, Functor)
```
Using the free monad, values of type `Free Add Var` represents
a language with operations formed by from the `Add` syntax and
variables from the type `Var`, which are `String` values for
simplicity.
```haskell
type Var = String
```
In this setting, the expression `x + (y + z)` is represented by the
following:
```haskell ignore
Op (Add (Var "x") (Op (Add (Var "y") (Var "z"))))
```
This is somewhat cumbersome notation, so instead we use a smart
constructor that injects syntax:

```haskell
add :: Add <: sig => Free sig a -> Free sig a -> Free sig a
add x y = op (Add x y)
```
With this in place we can write:
```haskell
-- | >>> add (var "x") (add (var "y") (var "z")) :: Free Add Var
-- Op (Add (Var "x") (Op (Add (Var "y") (Var "z"))))
```


The semantics of a language with a signature `f` is given by providing
an _algebra_, which is a function of type `f a -> a`, where `a` is the
_carrier_ of the semantics.

For simplicity, we will interpret the syntax of `Add` into the type
`Int`.
```haskell
instance Alg Add Int where
  alg (Add x y) = x + y
```
In order to give a semantics to this expression, a suitable generator
must be given. For the purposes of illustration `env :: Var -> Eval`
is as follows:
```haskell
env :: Var -> Int
env var = case var of {"x" -> 27 ; "y" -> 15; _ -> 0}
```
Evaluating with this environment is achieved by invoking `eval`:
```haskell
-- | >>> eval env (add (var "x") (var "y") :: Free Add Var)
-- 42
```

# Modularity
## Modular Operations

Adding additional operations is achieved by composing functors. To add
the ability to multiply numbers the appropriate functor is introduced:
```haskell
data Mul k = Mul k k deriving (Show, Functor)

mul :: Mul <: sig => Free sig a -> Free sig a -> Free sig a
mul x y = op (Mul x y)
```
The associated algebra must also be defined:
```haskell
instance Alg Mul Int where
  alg (Mul x y) = x * y
```

Using `add` and `mul` together allows expressions with a flexible
type:

```haskell
-- | >>> add (var "x") (mul (var "y") (var "z")) :: Free (Add :+: Mul) Var
-- Op (L (Add (Var "x") (Op (R (Mul (Var "y") (Var "z"))))))

-- | >>> add (var "x") (mul (var "y") (var "z")) :: Free (Mul :+: Add) Var
-- Op (R (Add (Var "x") (Op (L (Mul (Var "y") (Var "z"))))))
```

The composition of algebras is handled automatically:

```haskell
-- | >>> eval env (add (var "x") (mul (var "y") (var "z")) :: Free (Mul :+: Add) Var)
-- 27
```

## Modular Semantics

Additional semantics can be given by simply creating new instances of
the `Alg` class. As before, it is good practice to create a `newtype`
that represents the carrier of interest.

For instance, consider a carrier that counts the number of multiplications
in an expression:

```haskell
newtype Muls = Muls Int deriving Show

instance Alg Add Muls where
  alg (Add (Muls x) (Muls y)) = Muls (x + y)

instance Alg Mul Muls where
  alg (Mul (Muls x) (Muls y)) = Muls (1 + x + y)
```

The generator required here wraps an element into a list by applying
`pure`, and adds a `Vars` constructor:
```haskell
muls :: Var -> Muls
muls x = Muls 0
```
Changing the generator involved is enough to retreive a different
semantics:
```haskell
-- | >>> eval muls (add (var "x") (mul (var "y") (var "z")) :: Free (Mul :+: Add) Var)
-- Muls 1
```

It is also possible to extract multiple semantics too:
```haskell
-- | >>> eval (env /\ muls) (add (var "x") (mul (var "y") (var "z")) :: Free (Mul :+: Add) Var)
-- (27,Muls 1)
```

# Semantics

## Evaluation Semantics

A natural semantics can often be given to a fragment of syntax,
and this is expressed using the `Eval` carrier.

```haskell
instance Alg Add (Eval Int) where
  alg (Add (Eval x) (Eval y)) = Eval (x + y)
instance Alg Mul (Eval Int) where
  alg (Mul (Eval x) (Eval y)) = Eval (x * y)
```

```haskell
-- | >>> eval (Eval . env) (add (var "x") (mul (var "y") (var "z")) :: Free (Mul :+: Add) Var)
-- Eval 27
```

## Bound Variables

Tracking bound variables can be achieved by the `Vars` carrier, which
requires the signature functors to be foldable.

```haskell
deriving instance Foldable Mul
deriving instance Foldable Add
```

When a functor has a foldable instance, a natural consequence is that
the variables can be easily collected:

```haskell
-- | >>> eval vars (add (var "x") (mul (var "y") (var "z")) :: Free (Mul :+: Add) Var)
-- Vars ["x","y","z"]
```

### Footnote

For the curious, this README file is a literate Haskell file:
```haskell
main = pure ()
```
