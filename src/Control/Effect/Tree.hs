{-# LANGUAGE DataKinds #-}

module Control.Effect.Tree where

import Control.Monad.Trans.Tree
import Control.Effect
import Control.Family.Algebraic
import Control.Effect.Alternative.Internal
import Control.Applicative

nondetTreeAlg
  :: Monad m
  => (forall x . oeff m  x -> m x)
  -> (forall x . Effs '[Empty, Choose] (TreeT m) x -> TreeT m x)
nondetTreeAlg oalg op
  | Just (Alg Empty)        <- prj op = empty
  | Just (Alg (Choose x y)) <- prj op = return x <|> return y

nondetTree :: Handler [Empty, Choose] '[] '[TreeT] '[[]]
nondetTree = handler runTreeA nondetTreeAlg