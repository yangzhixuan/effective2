{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.List.Kind where
import Data.Kind (Constraint)

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

type family ((xs :: [k]) :\\ (ys :: [k]))  :: [k] where
  xs :\\ '[]       = xs
  xs :\\ (y ': ys) = (Delete y xs) :\\ ys

type family Union (xs :: [k]) (ys :: [k]) :: [k] where
  Union xs ys = xs :++ (ys :\\ xs)

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x, All c xs)


