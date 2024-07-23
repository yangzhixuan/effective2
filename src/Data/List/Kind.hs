{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.List.Kind where
import Data.Kind (Constraint)

import GHC.TypeLits

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
  ElemIndex x (x ': xs) = 0
  ElemIndex x (_ ': xs) = 1 + (ElemIndex x xs)

type family ElemIndexes (xs :: [a]) (ys :: [a]) :: [Nat] where
  ElemIndexes '[]       ys = '[]
  ElemIndexes (x ': xs) ys = ElemIndex x ys ': ElemIndexes xs ys

type family Length (xs :: [a]) :: Nat where
  Length '[]       = 0
  Length (_ ': xs) = 1 + Length xs

type family Lookup (n :: Nat) (xs :: [a]) :: a where
  Lookup 0 (x ': xs) = x
  Lookup n (x ': xs) = Lookup (n - 1) xs

type family Foldr (f :: a -> b -> b) (k :: b) (xs :: [a]) :: b where
  Foldr f k '[]       = k
  Foldr f k (x ': xs) = f x (Foldr f k xs)
