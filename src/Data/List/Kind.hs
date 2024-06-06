{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.List.Kind where
import Data.Kind (Constraint)
import Data.Nat

type family (xs :: [k]) :++ (ys :: [k]) :: [k] where
  '[]       :++ ys = ys
  (x ': xs) :++ ys = x ': (xs :++ ys)

type family Insert (x :: k) (ys :: [k]) where
  Insert x '[]       = '[x]
  Insert x (x ': ys) = x ': ys
  Insert x (y ': ys) = y ': Insert x ys

type family Delete (x :: k) (ys :: [k]) :: [k] where
  Delete x '[]       = '[]
  Delete x (x ': ys) = ys
  Delete x (y ': ys) = y ': Delete x ys

type family Reverse (xs :: [k]) :: [k] where
  Reverse xs = Reverse' xs '[]

type family Reverse' (xs :: [k]) (sx :: [k]) :: [k] where
  Reverse' '[]       sx = sx
  Reverse' (x ': xs) sx = Reverse' xs (x ': sx)

type family ((xs :: [k]) :\\ (ys :: [k]))  :: [k] where
  xs :\\ '[]       = xs
  xs :\\ (y ': ys) = (Delete y xs) :\\ ys

type Union xs ys = xs :++ (ys :\\ xs)
type Inter xs ys = xs :\\ (xs :\\ ys)

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x, All c xs)

-- Find an index of an element in a `list'
-- The element must exist
-- This closed type family disambiguates otherwise overlapping
-- instances
type family ElemIndex (x :: a) (xs :: [a]) :: Nat where
  ElemIndex x (x ': xs) = Z
  ElemIndex x (_ ': xs) = S (ElemIndex x xs)