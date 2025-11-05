module StagingHelper where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State

type Code a = Up a

metaProg :: Code Int ! '[Put (Code Int), Get (Code Int)]
metaProg = do s <- get @(Code Int); put [|| $$s + 1 ||]; pure s