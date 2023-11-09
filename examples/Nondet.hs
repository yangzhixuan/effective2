{-# LANGUAGE DataKinds #-}

module Nondet where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Cut
import Control.Effect.Nondet

knapsack
  :: Members [Stop, Or] sig
  => Int -> [Int] -> Prog sig [Int]
knapsack w vs
  | w <  0 = stop
  | w == 0 = return []
  | w >  0 = do v <- select vs
                vs' <- knapsack (w - v) vs
                return (v : vs')


-- `list` is not a modular handler and uses `eval` directly
exampleNondet1 :: [[Int]]
exampleNondet1 = list $ knapsack 3 [3, 2, 1]
-- [[3],[2,1],[1,2],[1,1,1]]

-- `nondet` is a modular handler but does not
-- handle `once`. Here it is immaterial because `once`
-- does not appear in the program
exampleNondet2 :: [[Int]]
exampleNondet2 = handle nondet $ knapsack 3 [3, 2, 1]
-- [[3],[2,1],[1,2],[1,1,1]]

-- `backtrack` is modular, and is furthermore simply
-- the joining of the nondet algebra with an algebra
-- for once
exampleNondet3 = handle backtrack $ knapsack 3 [3, 2, 1]
-- [[3],[2,1],[1,2],[1,1,1]]

-- onceEx :: (Member Or sig, Member Once sig) => Prog sig Int

exampleOnce :: [Int]
exampleOnce = handle onceNondet p where
  p :: Members [Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))
-- ghci> exampleOnce
-- [1,2]

