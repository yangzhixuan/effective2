{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module Error where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog.Internal.TH

import Control.Effect
import Control.Effect.Catch
import Control.Effect.Throw
import Control.Effect.Except

monus :: Members '[Throw] sig => Int -> Int -> Prog sig Int
monus x y = do if x < y then throw else return (x - y)

safeMonus :: Members '[Throw, Catch] sig => Int -> Int -> Prog sig Int
safeMonus x y = catch (monus x y) (return 0)

example_monus = property $ do
  x <- forAll $ Gen.int $ Range.linear 1 1000
  y <- forAll $ Gen.int $ Range.linear 1 1000

  if (x < y)
    then handle except (monus x y) === Nothing
    else handle except (monus x y) === Just (x - y)

example_safeMonus = property $ do
  x <- forAll $ Gen.int $ Range.linear 1 1000
  y <- forAll $ Gen.int $ Range.linear 1 1000

  if (x < y)
    then handle except (safeMonus x y) === Just 0
    else handle except (safeMonus x y) === Just (x - y)

examples = $$(discoverPrefix "example_")
