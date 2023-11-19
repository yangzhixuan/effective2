{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.List.Kind where

type family (xs :: [k]) :++ (ys :: [k]) :: [k] where
  '[]       :++ ys = ys
  (x ': xs) :++ ys = x ': (xs :++ ys)

type family Insert (x :: k) (ys :: [k]) where
  Insert x '[]       = '[x]
  Insert x (x ': ys) = x ': ys
  Insert x (y ': ys) = y ': Insert x ys


type family Union (xs :: [k]) (ys :: [k]) :: [k] where
  Union '[]       ys = ys
  Union (x ': xs) ys = Insert x (Union xs ys)