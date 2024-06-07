module Main where

import Hedgehog
import Hedgehog.Main

import Error
import Nondet
-- import State
-- import Parser
-- import Graded ()

main :: IO ()
main = defaultMain $ fmap checkParallel
  [ Error.examples
  , Nondet.examples
--  , State.examples
--  , Parser.examples
  ]
