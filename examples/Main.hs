module Main where

import Hedgehog
import Hedgehog.Main
import Hedgehog.Internal.TH

import qualified Error
main :: IO ()
main = defaultMain $ fmap checkParallel
  [ Error.examples
  ]

