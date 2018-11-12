# Effective

The `effective` library is an effect handlers library that is designed
to allow users to define and interpret their own languages and
effects.

This library requires several language extensions to be used properly,
and can be imported via `Control.Effect`:
```haskell
{-# LANGUAGE MultiParamTypeClasses #-}
module Readme where
import Control.Effect
```
This `README` file is a literate Haskell file that can be downloaded
separately.

Consider a language that can only perform addition.
```haskell
data Add_ k = k :+ k deriving Show

instance Functor Add_ where
  fmap f (x :+ y) = f x :+ f y
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
Op (Add_ (Var "x") (Op (Var "y") (Var "z")))
```
The semantics of a language with a signature `f` is given by providing
an _algebra_, which is a function of type `f a -> a`, where `a` is the
_carrier_ of the semantics.


In practice this is achieved by creating a type class instance.
The natural carrier for evaluating arithmetic expressions will be
called `Eval`:
```haskell
newtype Eval = Eval Int deriving Show
```
The instance for the `Add_` language that interprets into the `Eval`
carrier is:
```haskell
instance Alg Add_ Eval where
  alg (Eval x :+ Eval y) = Eval (x + y)
```
In order to give a semantics to this expression, a suitable generator
must be given. In this case we provide a function of type `Var ->
Int`:
```haskell
-- | >>> eval (\var -> Eval (case var of {"x" -> 27 ; "y" -> 15; _ -> 0})) (Op ((Var "x") :+ (Var "y")))
-- Eval 42
```
