{-|
Module      : Data.CutList
Description : CutList
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Data.CutList where

import Control.Applicative ( Alternative((<|>), empty) )
import Control.Monad ( ap )

-- | Lists that terminate with either a `Nil`, which
-- can have further values appended to them, or `Zero`,
-- which cannot have further values appended.
data CutList a = a :< CutList a | Nil | Zero
  deriving Functor

-- | Converts a list into a `CutList`.
toCutList :: [a] -> CutList a
toCutList (x : xs) = x :< toCutList xs
toCutList []       = Nil

-- | Converts a `CutList` into a list.
fromCutList :: CutList a -> [a]
fromCutList (x :< xs) = x : fromCutList xs
fromCutList _         = []

instance Semigroup (CutList a) where
  Zero      <> _  = Zero
  Nil       <> ys = ys
  (x :< xs) <> ys = x :< (xs <> ys)

instance Monoid (CutList a) where
  mempty = Nil

instance Applicative CutList where
  pure x = x :< Nil
  (<*>)  = ap

instance Monad CutList where
  mx >>= f = join (fmap f mx) where
    join :: CutList (CutList a) -> CutList a
    join ((x :< xs) :< xss) = x :< join (xs :< xss)
    join (Nil  :< xss) = join xss
    join (Zero :< _)   = Zero
    join Nil           = Nil
    join Zero          = Zero

instance Alternative CutList where
  empty            = Nil
  Zero      <|> _  = Nil
  Nil       <|> ys = ys
  (x :< xs) <|> ys = x :< (xs <|> ys)
