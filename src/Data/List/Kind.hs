{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Data.List.Kind where

type family (xs :: [k]) :++ (ys :: [k]) :: [k] where
  (x ': xs) :++ ys = x ': (xs :++ ys)
  '[]       :++ ys = ys

