{-# LANGUAGE DataKinds #-}

module State where

import Control.Effect
import Control.Effect.State
import Control.Effect.Catch
import Control.Effect.Throw
import Control.Effect.Except
import Control.Monad (replicateM)
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.State.Lazy as S


exampleState :: (Int, ())
exampleState = handle (state 41) incr
-- ghci> exampleState
-- (42,())

catchDecr
  :: Members [Put Int, Get Int, Throw, Catch] sig
  => Prog sig ()
catchDecr = do
  decr
  catch (decr >> decr)
        (return ())


globalState
  :: s -> Handler [Throw, Catch, Put s, Get s, Local s]
          [MaybeT,  S.StateT s]
          [((,) s), Maybe] '[]
globalState s = except <&> state s

exampleGlobalState :: (Int, Maybe ())
exampleGlobalState = handle (globalState 2) catchDecr
-- This is global state because the `Int` is decremented
-- twice before the exception is thrown.
--
-- ghci> exampleGlobalState
-- (0,Just ())


localState
  :: s -> Handler
          [Put s, Get s, Local s, Throw, Catch]
          [S.StateT s, MaybeT]
          [Maybe, ((,) s)]
          '[]
localState s = state s <&> except

exampleLocalState :: Maybe (Int, ())
exampleLocalState = handle (localState 2) catchDecr
-- With local state, the state is reset to its value
-- before the catch where the exception was raised.
--
-- ghci> exampleLocalState
-- Just (1,())

catchDecr'
  :: Members [Put Int, Get Int, Throw, Catch] sig
  => Prog sig ()
catchDecr' = do
  decr
  catch (decr >> decr)
        (replicateM 44 incr >> return ())

-- For instance you might want to allocate a bit more memory ...
-- and a bit more ... and so on.
exampleRetry1 :: (Int, Maybe ())
exampleRetry1 = handle (retry <&> state 2) catchDecr'


incr
  :: Members [Put Int, Get Int] sig
  => Prog sig ()
incr = do x <- get
          put @Int (x + 1)

decr
  :: Members [Put Int, Get Int, Throw] sig
  => Prog sig ()
decr = do x <- get
          if (x > 0)
            then put @Int (x - 1)
            else throw

