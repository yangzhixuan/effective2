{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Throw where

import Control.Effect

data Throw k where
  Throw :: Throw k
  deriving Functor

throw :: Member Throw sig => Prog sig a
throw = injCall (Alg Throw)
