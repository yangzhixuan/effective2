{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.List.TypeLevel where

type family (xs :: [k]) :++ (ys :: [k]) :: [k] where
  (x ': xs) :++ ys = x ': (xs :++ ys)
  '[]       :++ ys = ys

