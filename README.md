# Effective

The `effective` library is an effect handlers library that is designed to allow
users to define and interpret their own languages and effects.
This library incorporates support for both algebraic and scoped effects,
and is an implementation of the theory presented in [Modular Models of
Monids with Operations](https://dl.acm.org/doi/10.1145/3607850) by Yang and Wu.

## Preamble

Various language extensions are useful when using the `effective` library:
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ImplicitParams #-}
```
The `effective` library is imported via `Control.Effect`:
```haskell
import Control.Effect
import Control.Effect.State
import Control.Monad.Trans.State.Lazy (StateT)

import Prelude hiding (putStrLn, getLine)
import qualified Prelude

```
We will implement the `Teletype` example, a rite of passage for monadic IO
[^Gordon1992].


First, the operations that need to be simulated are
implemented:
```haskell
data GetLine k  = GetLine (String -> k) deriving Functor
data PutStrLn k = PutStrLn String k     deriving Functor

getLine :: Member GetLine sig => Prog sig String
getLine = injCall (Alg (GetLine return))

putStrLn :: Member PutStrLn sig => String -> Prog sig ()
putStrLn str = injCall (Alg (PutStrLn str (return ())))
```

Now a sample program that will use these operations.
Here is a simple echo program that will continue
to echo the input to the output until there is no
more input received by `getLine`:
```haskell
echo :: Prog [GetLine, PutStrLn] ()
echo = do str <- getLine
          case str of
            [] -> return ()
            _  -> do putStrLn str
                     echo
```
This program can be understood as an entirely syntactic representation of the
program. To execute it, it must be handled by an appropriate handler.

The most obvious interpretation of `getLine` and `putLine` is to
invoke their corresponding values from the prelude.
```haskell
algIO :: Effs [GetLine, PutStrLn] IO a -> IO a
algIO eff
  | Just (Alg (GetLine k))    <- prj eff =
      do str <- Prelude.getLine
         return (k str)
  | Just (Alg (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k

algPutStrLn :: Effs '[PutStrLn] IO a -> IO a
algPutStrLn eff
  | Just (Alg (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k
```
This algebra can be used to execute into the IO Monad using `handleM' algIO`:

```haskell
exampleIO :: IO ()
exampleIO = eval algIO echo
```
Since forwarding to IO is a usual case, `effective` provides `handleIO`
as a convenience function.
```haskell
-- exampleIO' :: IO ()
-- exampleIO' = handleIO echo
```

The power of effects is in their ability to intercept and reinterpret operations.
For instance, another way to implement `getLine` is in terms of |put| and
|get| from a state containing a list of strings:
```haskell
getLineState
  :: forall oeff . Members '[Get [String], Put [String]] oeff 
  => Handler '[GetLine] '[] '[] oeff
getLineState = reinterp malg where
  malg :: forall x m . Effs '[GetLine] m x -> Prog oeff x
  malg eff | Just (Alg (GetLine k)) <- prj eff =
    do xss <- get
       case xss of
         []        -> return (k "")
         (xs:xss') -> do put xss'
                         return (k xs)
```

The operations |Get| and |Put| can themselves interpeted in multiple ways. The
most standard is to use the `state` handler in `Effect.Control.State`:
```
state :: s -> Handler [Put s, Get s, Local s] '[S.StateT s] '[((,) s)] oeff
```
The output of the `getLineState` handler can be piped into the `state` handler
to produce a new handler:

```haskell
getLinePure :: [String] -> Handler '[GetLine] '[StateT [String]] '[(,) [String]] oeff
getLinePure str = pipe @'[Get [String], Put [String]] @'[] getLineState (state str)
```
Now we have a means of executing a program that contains only a |GetLine| effect,
and extracting the resulting string:
```
handle (getLinePure ["hello", "world"]) :: Prog '[GetLine] a -> ([String], a)
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

Now this can be handled with `handleM'` to output to IO, while redirecting the
input to come from a pure list:
```haskell
exampleO :: IO ([String], ())
exampleO = handleM' algPutStrLn (getLinePure ["hello", "world"]) echo
```
This outputs:
```
ghci> exampleO
hello
world
([],())
```

[^Gordon1992]: A. Gordon. Functional Programming and Input/Output. PhD Thesis, King's College London. 1992
