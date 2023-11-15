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
import Control.Monad

import Prelude hiding (putStrLn, getLine)
import qualified Prelude

```
We will implement the `Teletype` and `FileSystem` example, due to
[Swierstra](https://doi.org/10.1017/S0956796808006758),
which demonstrates how to treat IO operations as a DSL.

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
This program can be undrestood as an entirely syntactic representation of the
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
This algebra can be used to execute into the IO Monad using `handleM algIO`:

```haskell
teletypeIO :: Handler [GetLine, PutStrLn] '[] '[] [GetLine, PutStrLn]
teletypeIO = trivialH

trivialH :: Handler eff '[] '[] eff
trivialH = interp (\alg -> alg)

-- handleIO :: Handler effs0 ts0 fs0 [GetLine, PutStrLn]
--                                     -> Prog effs0 a0 -> IO (Data.Functor.Composes.Composes fs0 a0)
-- handleIO = handleM algIO

exampleIO :: IO ()
exampleIO = handleM algIO teletypeIO echo

main :: IO ()
main = exampleIO
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

One way to deal with this is to fuse the `getLinePure` handler with `trivialH`,
so that `PutStrLn` can be exposed:
```haskell
teletypeO
  :: [String] 
  -> Handler '[GetLine, PutStrLn]
             '[StateT [String]]
             '[(,) [String]] '[PutStrLn]
teletypeO str = fuse @'[] @'[] @'[PutStrLn] (getLinePure str) (trivialH @'[PutStrLn])
```
Now this can be handled with `handleM` to output to IO, while redirecting the input
from a pure list:
```haskell
exampleO = handleM algPutStrLn (teletypeO ["hello", "world"]) echo
```
This outputs:
```
ghci> exampleO
hello
world
([],())
```



The following performs fusion, which is not exactly what we want here.
```haskell
huh :: [String] 
    -> Handler '[GetLine, Put [String], Get [String], Local [String]] 
               '[StateT [String]] '[(,) [String]] '[]
huh str = fuse @'[Get [String], Put [String]] @'[] getLineState (state str)
```
