{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Alternative
  ( module Control.Effect.Alternative
  , module Control.Effect.Alternative.Type
  ) where

import Control.Effect.Alternative.Type

import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad.Trans.Class

instance (Member Choose sigs, Member Empty sigs)
  => Alternative (Prog sigs) where
  {-# INLINE empty #-}
  empty = call (Alg Empty)

  {-# INLINE (<|>) #-}
  xs <|> ys = call (Scp (Choose (fmap return xs) (fmap return ys)))

alternativeAlg
  :: (MonadTrans t, Alternative (t m), Monad m)
  => (Algebra oeffs m)
  -> (Algebra [Empty , Choose] (t m))
alternativeAlg oalg eff
  | (Just (Alg Empty))          <- prj eff = empty
  | (Just (Scp (Choose xs ys))) <- prj eff = xs <|> ys