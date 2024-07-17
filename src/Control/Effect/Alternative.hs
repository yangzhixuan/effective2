{-# LANGUAGE DataKinds #-}

module Control.Effect.Alternative
  ( module Control.Effect.Alternative
  , module Control.Effect.Alternative.Type
  ) where

import Control.Effect.Alternative.Type

import Control.Effect
import Control.Family.Algebraic
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad.Trans.Class

alternativeAlg
  :: (MonadTrans t, Alternative (t m), Monad m)
  => (Algebra oeffs m)
  -> (Algebra [Empty , Choose] (t m))
alternativeAlg oalg eff
  | (Just (Alg Empty))        <- prj eff = empty
  | (Just (Alg (Choose x y))) <- prj eff = return x <|> return y