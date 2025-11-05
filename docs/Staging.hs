{-# OPTIONS_GHC -ddump-splices  #-}
module Staging () where

import Control.Effect
import Control.Effect.Nondet
import Control.Effect.CodeGen
import Data.Functor.Identity
import Control.Effect.State
import StagingHelper

--------------------------------------------------------------------------------

{- Although `effective` is built with performance in consideration, effect handling
in general unavoidably introduce some performance cost.  -}

pyth :: Int -> [(Int, Int, Int)]
pyth upbound = handle list $ do
    x <- choice upbound
    y <- choice upbound
    z <- choice upbound
    if x * x + y * y == z * z then return (x, y, z) else empty
  where
    choice 0 = empty
    choice n = choice (n - 1) <|> pure n

--------------------------------------------------------------------------------

{- Performance benchmark for a range of handler libraries on @pyth 32@:
(ghc -O enabled for all tests)
      eff:
        28.4 ms ± 2.1 ms
      heftia:
        4.96 ms ± 297 μs
      freer:
        3.81 ms ± 248 μs
      mp:
        2.62 ms ± 131 μs
      ev:
        944  μs ±  60 μs
      effective.List:          <- we are here
        782  μs ±  60 μs
      fused:
        293  μs ±  15 μs
      mtl-logict:
        284  μs ±  27 μs
-}

--------------------------------------------------------------------------------

{- All of these libraries are much slower than the following native Haskell code:
      Haskell native:
        96.2 μs ± 7.8 μs
-}
native :: Int -> [(Int, Int, Int)]
native n = [ (x, y, z) | x <- [1 .. n],
                         y <- [1 .. n],
                         z <- [1 .. n],
                         x * x + y * y == z * z ]
{- For reference, comparable C code is ~4 times faster still:
      Comparable C code (with `clang -O`)
        25.8 μs ± 6.2 µs
-}

--------------------------------------------------------------------------------

{- The performance overhead of effect handling can be eliminated by using the
_code generation_ effect of `effective`.  -}

choose :: Int -> [Int]
choose n = $$(stage pushGen $
  genIf [|| n > 0 ||]
    (up [|| choose (n - 1) ||] <|> return [||n||])
    empty
  )

pythStaged :: Int -> [(Int, Int, Int)]
pythStaged n = $$(stage pushGen $
  do x <- up ([|| choose n||])
     y <- up ([|| choose n||])
     z <- up ([|| choose n||])
     genIf [|| $$x * $$x + $$y * $$y == $$z * $$z ||]
       (return [|| ($$x, $$y, $$z) ||])
       empty
  )
{- This version is as fast as native code:
      Haskell native:
        96.2 μs ± 7.8 μs
      effective staged:
        96.2 μs ± 7.3 μs
-}

--------------------------------------------------------------------------------

{- Generated code is essentially 3-nested loops: -}

pythGenerated :: Int -> [(Int, Int, Int)]
pythGenerated n_a2gZ =
  foldr (\ a_a7Vm ms_a7Vn ->
    (foldr (\ a_a7Vo ms_a7Vp ->
       (foldr (\ a_a7Vq ms_a7Vr ->
          (if (((a_a7Vm * a_a7Vm) + (a_a7Vo * a_a7Vo)) == (a_a7Vq * a_a7Vq))
             then
                 ((a_a7Vm, a_a7Vo, a_a7Vq) :  ms_a7Vr)
             else
                  ms_a7Vr))
           (ms_a7Vp) (choose n_a2gZ)))
        (ms_a7Vn) (choose n_a2gZ)))
      [] (choose n_a2gZ)


--------------------------------------------------------------------------------

{- Staging even does list-fusion by construction: -}

map2 :: (b -> c) -> (a -> b) -> [a] -> [c]
map2 g f xs = $$(stage pushGen $
  fmap (\x -> [|| g $$x ||]) (fmap (\x -> [|| f $$x ||]) (up [|| xs ||])))

-- map2 g f xs = foldr (\ a ms -> (g (f a) : ms)) [] xs

--------------------------------------------------------------------------------

{- What is interesting here is that we retain a monadic interface
at compile time for effectful programming:

>  do x <- up ([|| choose n||])
>     y <- up ([|| choose n||])
>     z <- up ([|| choose n||])
>     genIf [|| $$x * $$x + $$y * $$y == $$z * $$z ||]
>       (return [|| ($$x, $$y, $$z) ||])
>       empty

This is a non-trivial achievement because the type of _code of monadic
programs_ `Code (m a)` for a monad `m` is not itself a monad.  -}

--------------------------------------------------------------------------------

{- How did we solve this problem in `effective`?

(Heavily influenced by András Kovács [ICFP 2024])

1. We find a compile-time operation for each run-time effectul operation:
               Put (Code s)        ~>        Put s
               Throw (Code e)      ~>       Throw e
               Choose              ~>        Choose

2. We find a compile-time monad `n` for each run-time monad `m`:

> class n $~> m where
>   down :: n (Code a) -> Code (m a)

> instance (State (Code s))   $~>  (State s)   where ...
> instance (Except (Code e))  $~>  (Except e)  where ...

3. We use `effective` to work with (compile-time) programs using
  compile-time effects, interpreting them as compile-time monads, which are
  then `down`-ed to run-time monadic programs only at the end.  -}

--------------------------------------------------------------------------------

{- The usual flexibility of effect handlers -- one program multiple
   interpretations -- is still kept.

  In another module we have:

-- metaProg :: Code Int ! '[Put (Code Int), Get (Code Int)]
-- metaProg = do s <- get @(Code Int); put [|| $$s + 1 ||]; pure s
-}

p :: StateT Int Identity Int
p = $$(stage (stateAT @(Code Int)) metaProg)
-- p = StateT (\ s -> Identity (s, (s + 1)))

{- We can define a handler that inserts a let-binding for every put: -}

q :: StateT Int Identity Int
q = $$(let letPut :: forall s. AlgTrans '[Put (Up s)] '[Put (Up s), CodeGen] '[] Monad
           letPut = interpretAT (\(Put (s :: Up s) k) ->
             do s' <- genLet s
                put s'
                return k)
       in stage (letPut @Int `fuseAT` stateAT @(Code Int))
                metaProg)
-- q = StateT (\ s -> Identity (let x_ab9f = (s + 1) in (s, x_ab9f)))

--------------------------------------------------------------------------------
{-
  There are more things in the library:

  1. generate tail-recursive code;

  2. an operation `up :: Code (m a) -> n (Code a)`, which is needed
     for interoperability between compile-time and run-time effectful
     programs.

Future work:
  * eliminate the 'noise' in meta-programs by _stage inference_.
-}

