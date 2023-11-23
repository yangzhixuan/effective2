# Effective

The `effective` library is an effect handlers library that is designed to allow
users to define and interpret their own languages and effects.
This library incorporates support for both algebraic and scoped effects,
and is an implementation of the theory presented in [Modular Models of
Monoids with Operations](https://dl.acm.org/doi/10.1145/3607850) by Yang and Wu.

This README is a literate Haskell file and therefore can be executed. You can interact
its contents with `cabal repl readme` and follow the examples.


Working with IO
----------------

The `Teletype` example is a rite of passage for monadic IO [^Gordon1992] where
the challenge is to show how IO of reading from and writing to the terminal can
be achieved. A program that interacts with the terminal is `echo`. This is a
simple program that will continue to echo the input obtained by `getLine` is
output to the terminal using `putStrLn` until a blank line is received by
`getLine`:
```haskell
echo' :: Prog' [GetLine, PutStrLn] ()
echo' = do str <- getLine
           case str of
             [] -> return ()
             _  -> do putStrLn str
                      echo'
```
The type signature says that this is a program that requires
both `GetLine` and `PutStrLn` operations.

The most obvious interpretation of `getLine` and `putLine` is to invoke their
corresponding values from the prelude. Indeed, when all of the operations of a
program are standard Prelude IO operations, it is enough to simply evaluate the
program using `evalIO`:
```haskell
exampleIO' :: IO ()
exampleIO' = evalIO echo'
```
This will execute the `echo` program where input provided on the
terminal user is immediately echoed back out to the terminal.


Working with State
-------------------

A pure state effect is provided in `Effect.Control.State`, which supports
`get` and `put` as operations that are indicated by `Get s` and `Put s`
in a signature.

For example, here is a program that increments the number in a state
and returns it:
```haskell
incr' :: Prog' [Put Int, Get Int] ()
incr' = do x <- get
           put @Int (x + 1)
```
In order to keep the program modular, the effects in `effs` are given by a
constraint on the input type, saying that `Put Int` and `Get Int` are its
members.

This program can be executed by using a handler. For state, the usual
handler is given by:
```haskell ignore
state :: s -> Handler '[Put s, Get s, Local s]  -- input effects
                      '[StateT s]               -- semantic transformer
                      '[((,) s)]                -- output carrier
                      '[]                       -- output effects
```
The signature of the handler tells us how it behaves:
* The input effects are `Put s`, `Get s`, and `Local s`.
* The internal semantics are provided by the state transformer `StateT s`.
* The output of this handler wraps the result with the functor `((,) s)`
* The output effects are empty
When `state s` is used to handle a program of type `Prog effs a`,
the output will be the functor `((,) s)` applied to the value of the program
`a`, which is simply `(s, a)`.

Executing the `incr` program with this handler can be achieved as follows:
```haskell ignore
ghci> handle (state 41) incr :: (Int, ())
(42,())
```
Since the program has type `Prog effs ()`, with a pure value of `()`,
the result of applying the handler is `((,) Int)` applied to `()`,
thus giving back `(Int, ())`.

The `state` handler returns the final state as well as the final
return value of the program
```haskell ignore
ghci> handle (state "Hello!") (do xs <- get @String; return (length xs))
("Hello!",6)
```
A variation of the `state` handler is `state_`, which does not return
the final state:
```haskell ignore
state_ :: s -> Handler [Put s, Get s, Local s] '[StateT s] '[] '[]
```
Here the final output carrier is `'[]`, and so applying this to a program
of type `Prog sig a` will simply return a value of type `a`.
```haskell ignore
ghci> handle (state_ "Hello!") (do xs <- get @String; return (length xs))
6
```

All Effects Must Be Handled
----------------------------

The effect of `handle h p` is to use the handler `h` to remove _all_ of the
effects in interpreting the program `p`. This relates to both the effects
of the program and effects output by a handler.
Trying to apply a handler that does not fully evaluate the effects in `p` will
result in a type error.
For example, `getLineLength` is a program that gets a single line and
returns its length:
```haskell
getLineLength :: Prog' '[GetLine] Int
getLineLength = do xs <- getLine
                   return (length xs)
```
This program can executed using `evalIO`:
```haskell ignore
ghci> evalIO (do xs <- getLine; return (length xs))
Hello
5
```
This program cannot be handled with a state handler:
```haskell ignore
ghci> handle (state "Hello") getLineLength

<interactive>:19:24: error: [GHC-39999]
    • No instance for ‘Member' GetLine '[] (ElemIndex GetLine '[])’
        arising from a use of ‘getLineLength’
    • In the second argument of ‘handle’, namely ‘getLineLength’
      In the expression: handle (state "Hello") getLineLength
      In an equation for ‘it’: it = handle (state "Hello") getLineLength
```
This is essentially saying that `GetLine` is not supported by the state
handler.


Working with IO and State
-------------------------

Now suppose that the task is to count the number of times `getLine` is called.
One approach is to change the `echo` program, and write something like
`echoCount`, where an `incr` has been added after each `getLine`:
```haskell
echoCount :: Members [GetLine, Get Int, Put Int, PutStrLn] sig => Prog sig ()
echoCount =
  do str <- getLine
     incr
     case str of
       [] -> return ()
       _  -> do putStrLn str
                echoCount
```
To execute such a program that uses both state and IO
requires a handler that is specialised to deal with IO:
```haskell
exampleEchoCount :: IO (Int, ())
exampleEchoCount = handleIO (state (0 :: Int)) echoCount
```
When this is executed, it counts the number of lines received:
```haskell ignore
ghci> exampleEchoCount
Hello
Hello
world!
world!

(3,())
```
This program does the job but it is rather crude: asking developers to
add `incr` after every `getLine` is only asking for trouble. One
alternative would be to define a variation of `getLine` that
incorporates `incr`, but that is hardly better.

Better would be to allow a different interpretation of `getLine` that
automatically increments a variable: then the `echo` program could
remain exactly the same.


Intercepting Operations
-----------------------

The power of effects is in their ability to intercept and reinterpret
operations.
Here is how to write a handler that intercepts a `getLine` operation,
only to perform it again while also incrementing a counter in the state:
```haskell
getLineIncr
  :: forall sig . Members '[GetLine, Get Int, Put Int] sig => Handler '[GetLine] '[] '[] sig
getLineIncr = reinterp malg where
  malg :: forall x m . Effs '[GetLine] m x -> Prog sig x
  malg eff | Just (Alg (GetLine k)) <- prj eff =
    do xs <- getLine
       incr
       return (k xs)
```
The handler says that it will deal with `[GetLine]` as an input effect,
but and will output the effects `[GetLine, Get Int, Put Int]`.

Now the task is to connect this handler with `state`. This can
be achieved with a `pipe`:
```haskell
getLineIncrState :: Handler '[GetLine] '[StateT Int] '[(,) Int] '[GetLine]
getLineIncrState
  = pipe @'[Get Int, Put Int] @'[GetLine]
      getLineIncr
      (state (0 :: Int))
```

For another example, it might be useful to test the `getLineLength` program
without having to supply input from the terminal, but rather, directly from a
list of strings supplied by state. Here is how `getLine` can be interpreted in
terms of the operations `get` and `put` from a state containing a list
of strings:
```haskell
getLineState
  :: forall sig . Members [Get [String], Put [String]] sig => Handler '[GetLine] '[] '[] sig
getLineState = reinterp malg where
  malg :: forall x m . Effs '[GetLine] m x -> Prog sig x
  malg eff | Just (Alg (GetLine k)) <- prj eff =
    do xss <- get
       case xss of
         []        -> return (k "")
         (xs:xss') -> do put xss'
                         return (k xs)
```
The signature of `getLineState` says that it is a handler that recognises
`GetLine` operations and interprets them in terms of some output effects in
`oeff`, which consist of `Get [String]` and `Put [String]`. Reinterpeting
effects in terms of other, more primitive, effects allows other handlers to
deal with those more primitive effects.

The `getLineState` handler will process the `GetLine` effect in the
echo program, and in so doing will output `Get [String]` and `Put [String]`
effects. These can be handled by a state handler. The output of the
`getLineState` handler can be piped into the `state` handler to produce
a new handler. Here are two variations:
```haskell
getLinePure_ :: [String] -> Handler '[GetLine] '[StateT [String]] '[] '[]
getLinePure_ str = pipe @'[Get [String], Put [String]] @'[] getLineState (state_ str)

getLinePure :: [String] -> Handler '[GetLine] '[StateT [String]] '[(,) [String]] '[]
getLinePure str = pipe @'[Get [String], Put [String]] @'[] getLineState (state str)
```
Now we have a means of executing a program that contains only a |GetLine| effect,
and extracting the resulting string:
```haskell ignore
handle (getLinePure ["hello", "world!"]) :: Prog '[GetLine] a -> ([String], a)
```
Executing this will get the first line in the list of strings and return its length,
and the same program can be executed either processed with IO, o
```haskell ignore
ghci> handle (getLinePure ["Hello", "world!"]) (do xs <- getLine; return (length xs))
(["world!"],5)
```


This cannot be applied to the `echo` program, because the type of echo indicates
that the program also uses the `PutStrLn` effect, which must also be handled.
Trying to do so returns a type error:
```
ghci> :t handle (getLinePure ["hello", "world"]) echo

<interactive>:1:41: error: [GHC-83865]
    • Couldn't match type: '[PutStrLn]
                     with: '[]
      Expected: Prog '[GetLine] ()
        Actual: Prog [GetLine, PutStrLn] ()
    • In the second argument of ‘handle’, namely ‘echo’
      In the expression: handle (getLinePure ["hello", "world"]) echo
```
This is saying that GHC has no way to handle the `PutStrLn` effect
using this handler.

However, this can be handled with `handleIO` to output to IO, while redirecting the input to come from a pure list:
```haskell
exampleO :: IO ()
exampleO = handleIO (getLinePure_ ["hello", "world"]) echo

exampleO' :: IO Int
exampleO' = handleIO (getLinePure_ ["hello", "world!"]) getLineLength'

getLineLength' :: Prog' '[GetLine] Int
getLineLength' = do xs <- getLine
                    return (length xs)
```
This outputs:
```
ghci> exampleO
hello
world
```

```haskell
putStrLnWriter :: forall sig . Members '[Tell [String]] sig => Handler '[PutStrLn] '[] '[] sig
putStrLnWriter = reinterp malg where
  malg :: forall x m . Effs '[PutStrLn] m x -> Prog sig x
  malg eff | Just (Alg (PutStrLn str k)) <- prj eff =
    do tell [str]
       return k
```
Running the `echo` program will still need to output values to
the terminal

```haskell
-- teletypePure :: forall sig . Members '[Tell [String], Get [String], Put [String]] sig => Handler [PutStrLn, GetLine] '[] '[] sig
-- teletypePure = putStrLnWriter <&&> getLineState
```

```haskell
incrInput :: Prog' '[Put [String], GetLine] String
incrInput = do put ["Hello", "world"]
               xs <- getLine
               return xs
```

Grades vs Members Only
-----------------------

A different way of using this library is to use _graded monads_.
This offers a bottom-up type inference for programs rather than a
top-down one. The types of programs are more precise making it
harder to make mistakes, but also harder to write since the
types are less forgiving!

There are three scenarios to consider when trying to engineer a fit between a
program (shaft) of type `Prog effs a` and a handler (hole) of type `Handler
ieffs ts fs oeffs`, depending on how their interfaces correspond:

1. *Transition* (`effs = ieffs`): The program and the handler have the same
   signatures, up to reordering. Every effect is handled sequentially,
   from left to right in the order dictated by the handler.
2. *Clearance* (`effs < ieffs`): The handler can deal with more operations than
   required by the program. In these situations the handler or the program can
   be weakened
3. *Interference* (`effs > ieffs`): The handler cannot deal with all the operations
   exposed by the program. Any residual effects will have to be handled later.

When there is transition between program and handler, there may be a difference
in the orders of the effects presented in the signatures. The philosophy of 
effect handlers is that a program can be handled in different ways to create
different semantics. Although it is reasonable for a program to insist on a
particular order in which certain effects should be handled, the `effective`
library leaves this choice entirely to the handler.

When there is clearance between program and handler, the operations given by
`effs` are all members of `ieffs` as described by a `Members effs ieffs`
constraint. From the library perspective there is a choice of whether
to weaken the program or weaken the handler to create a transition. There
are two main strategies to describing programs and handlers that lead
to a decision on which to weaken:

* *Top-down* (members): With a top-down strategy, the handlers dictate the
  effects that the program accepts.

* *Bottom-up* (graded)

Weakening
the program means that the `effs` signature is increased to match `ieffs`,
thus causing more cases that should be scrutinised even though they are known
to be unusued. However, 





The examples above all compile with the `QualifiedDo` language
extension enabled. This simplifies the type signatures of
both programs and handlers that use effects.
Working without it is also possible by writing the required
constraints using `Members`.
```haskell
echo :: Prog' [GetLine, PutStrLn] ()
echo = do str <- getLine
          case str of
            [] -> return ()
            _  -> do putStrLn str
                     echo

exampleIO :: IO ()
exampleIO = evalIO echo

incr :: Prog' [Get Int, Put Int] ()
incr = do x <- get
          put @Int (x + 1)


-- getLineIncr'
--   :: forall oeff . Members '[GetLine, Get Int, Put Int] oeff
--   => Handler '[GetLine] '[] '[] oeff
getLineIncr'
  :: Handler '[GetLine] '[] '[] [GetLine, Get Int, Put Int]
getLineIncr' = reinterp malg where
  -- malg :: forall x m . Effs '[GetLine] m x -> Prog [GetLine, Get Int, Put Int] x
  malg eff | Just (Alg (GetLine k)) <- prj eff =
    do xs <- getLine
       incr'
       return (k xs)

```
Notice that writing in explicit members style requires the use of `getLine` and `putStrLn`. These are built with member constraints
themselves so that the code can be put together by building a
members contraint stack.

There are two ways of defining operations, which we will call _graded_ style and _member_ style.
In graded style operations the signature parameter to `Prog` says precisely which effects are present in a program:
```haskell ignore
throw :: Prog' '[Throw] a
throw = injCall (Alg Throw)

monus :: Int -> Int -> Prog' '[Throw] Int
monus x y = do if x < y then throw else return (x - y)
```
On the other hand, in member style an operation is in fact a family of operations where there is a `Member` constraint for effect:
```haskell ignore
throw' :: Member Throw sig => Prog sig a
throw' = injCall (Alg Throw)

monus' :: Member Throw sig => Int -> Int -> Prog sig Int
monus' x y = do if x < y then throw' else return (x - y)
```
Both are useful in different ways.

When programs are defined in member style the `sig` parameter exists for the purpose of unification.

Programs in graded style can be put together using a graded monad that takes the union of their signatures. 
If the signatures are stored as an unsorted list, then the signature order will follow the effects resulting in a _effect flow signature_. 

The definition of scoped operations fits neatly with member style operations. Consider `catch`:
```haskell ignore
catch
  :: (Member Catch sig) => Prog sig a -> Prog sig a -> Prog sig a
catch p q = injCall (Scp (Catch (fmap return (p))
                                (fmap return (q))))
```
The subprograms `p` and `q` will have their types unified with the output of `catch`. The type of the subprograms cannot be fixed in advance, which means that a `Member` constraint will be required. For the purposes of unification, it is convenient if the programs `p` and `q` have the same type signature, sharing `sig` with the overall type.

A more precise type to `catch` can be given where the two subprograms can have differing types, so long as they can be injected into the final type. 
```haskell ignore
catch
  :: ( Member Catch (Union sig'' '[Catch])
     , Injects sig  (Union sig'' '[Catch])
     , Injects sig' (Union sig'' '[Catch])
     , sig'' ~ Union sig sig' )
  => Prog sig a -> Prog sig' a -> Prog (Union sig'' '[Catch]) a
catch p q = injCall (Scp (Catch (fmap return (weakenProg p))
                                 (fmap return (weakenProg q))))
```


Language Extensions
--------------------

The `effective` library is best served with a few language extensions:


Imports
-------

This file has a number of imports:


[^Gordon1992]: A. Gordon. Functional Programming and Input/Output. PhD Thesis, King's College London. 1992

```haskell top
{-# LANGUAGE DataKinds #-}    -- Used for the list of effects
{-# LANGUAGE QualifiedDo #-}  -- For the bottom-up graded effects
```

```haskell top
import Control.Effect
import Control.Effect.State
import Control.Effect.Writer
import Control.Effect.IO
import Control.Monad.Trans.State.Lazy (StateT)

import Data.List.Kind
import Data.Functor.Composes
import Data.HFunctor.HComposes
import Data.SOP.Constraint
import Control.Monad.Trans.Class

import qualified Control.Monad.Graded as G

import Prelude hiding (putStrLn, getLine)
import qualified Prelude

main = return ()
```
