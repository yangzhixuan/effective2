```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}

module Graded where

import qualified Control.Monad.Graded as Graded
import Control.Effect
import qualified Control.Effect.State as State
import Control.Effect.State hiding (get, put)
import Control.Effect.Catch
import qualified Control.Effect.Throw as Throw
import Control.Effect.Throw hiding (throw)
import Control.Effect.Except
import Data.List.Kind (Union, Insert)
import Control.Monad (replicateM, replicateM_)
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.State.Lazy as S
```

A different way of using this library is to use _graded monads_.
This offers a bottom-up type inference for programs rather than a
top-down one.

To use the library in this way, the operations must be made monomorphic,
where the signature exposes only the effect that is used:

```haskell
get :: Prog '[Get s] s
get = State.get

put :: s -> Prog '[Put s] ()
put = State.put

throw :: Prog '[Throw] ()
throw = Throw.throw
```
The types of programs are more precise making it
harder to make mistakes, but also harder to write since the
types are less forgiving!

For example, the `incr` program is given as follows:
```haskell
incr :: Prog '[Get Int, Put Int] ()
incr = Graded.do
  x <- get
  put @Int (x + 1)
```
This program would not compile with the signature `Prog '[Put Int, Get Int] ()`,
where the effects are reversed.

A flow-graded program is not always compatible with conditionals,
since both branches of an `if_then_else_` must have the same type.
In the `decr` programm, one branch only exposes a `Put Int`
effect, whereas the other is `Throw`.
In order to make both branches have the same effects, one approach
is to use `return` with a suitable signature that allows the
branches to unify:
```haskell
decr :: Prog [Get Int, Put Int, Throw] ()
decr = Graded.do
  x <- get
  if (x > 0)
    then Graded.do return () :: Prog [Put Int, Throw] ()
                   put @Int (x - 1)
    else Graded.do return () :: Prog [Put Int, Throw] ()
                   throw
```
This can be fixed by using `RebindableSyntax` and offering a more
flexible version of conditionals that unifies the type of its
branches in the output. However at present GHC does not allow
rebinding of `case`.


```haskell
catchDecr :: Prog [Get Int, Put Int, Throw, Catch] ()
catchDecr = Graded.do
  decr
  catch'
    (Graded.do decr
               decr)
    (Graded.return ())

catchDecr' :: Prog [Get Int, Put Int, Throw, Catch] ()
catchDecr' = Graded.do
  decr
  catch'
    (Graded.do decr
               decr)
    (Graded.do replicateM_ 44 incr)

catch'
  :: ( Member Catch sig''
     , Injects sig  sig''
     , Injects sig' sig''
     , sig'' ~ Insert Catch (Union sig sig'))
  => Prog sig a -> Prog sig' a -> Prog sig'' a
catch' p q = injCall (Scp (Catch
  (fmap return (weakenProg p))
  (fmap return (weakenProg q))))


-- safeMonus :: Int -> Int -> Prog [Throw, Catch] Int
-- safeMonus x y = catch' (monus' x y) (return 0 :: Prog '[] Int)
```
