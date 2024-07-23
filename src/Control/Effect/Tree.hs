{-# LANGUAGE DataKinds #-}

module Control.Effect.Tree where

import Control.Monad.Trans.Tree
import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped
import Control.Effect.Alternative.Type
import Control.Applicative

nondetTreeAlg
  :: Monad m
  => (forall x . oeff m  x -> m x)
  -> (forall x . Effs '[Empty, Choose] (TreeT m) x -> TreeT m x)
nondetTreeAlg oalg op
  | Just (Alg Empty)          <- prj op = empty
  | Just (Scp (Choose xs ys)) <- prj op = xs <|> ys

nondetTree :: Handler [Empty, Choose] '[] (TreeT) []
nondetTree = handler runTreeA nondetTreeAlg