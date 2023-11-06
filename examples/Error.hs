{-# LANGUAGE DataKinds #-}

module Error where

import Control.Effect
import Control.Effect.Catch
import Control.Effect.Throw
import Control.Effect.Except

monus 
  :: Members [Throw, Catch] sig
  => Int -> Int -> Prog sig Int
monus x y = do if x < y then throw else return (x - y)

safeMonus 
  :: Members [Throw, Catch] sig
  => Int -> Int -> Prog sig Int
safeMonus x y = do catch (monus x y) (return 0)


exampleExcept1, exampleExcept2, exampleExcept3, exampleExcept4 :: Maybe Int
exampleExcept1 = handle except (monus 2 4)
exampleExcept2 = handle except (monus 4 2)
exampleExcept3 = handle except (safeMonus 2 4)
exampleExcept4 = handle except (safeMonus 4 2)
-- ghci> exampleExcept1
-- Nothing
-- ghci> exampleExcept2
-- Just 2
-- ghci> exampleExcept3
-- Just 0
-- ghci> exampleExcept4
-- Just 2


