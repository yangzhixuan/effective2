module Main where

import Hedgehog
import Hedgehog.Main
import Hedgehog.Internal.TH

import qualified Error
import qualified Nondet
import qualified State
import qualified Parser
import qualified Graded
import qualified Transformers

main :: IO ()
main = defaultMain $ fmap checkParallel
  [ Error.examples
  , Nondet.examples
  , State.examples
  , Parser.examples
  ]
