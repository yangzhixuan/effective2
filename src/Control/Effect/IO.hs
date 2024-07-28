{-# LANGUAGE CPP #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MonoLocalBinds #-}
#if __GLASGOW_HASKELL__ <= 902
{-# LANGUAGE TypeFamilies #-}
#endif

module Control.Effect.IO where

import Control.Effect
import Control.Effect.Algebraic

import GHC.TypeLits

import qualified System.CPUTime
import Data.List.Kind



type GetLine = Alg GetLine'
data GetLine' k  = GetLine (String -> k) deriving Functor

getLine :: Members '[GetLine] sig => Prog sig String
getLine = call (Alg (GetLine return))


type PutStrLn = Alg PutStrLn'
data PutStrLn' k = PutStrLn String k     deriving Functor

putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = call (Alg (PutStrLn str (return ())))

type GetCPUTime = Alg (GetCPUTime')
data GetCPUTime' k = GetCPUTime (Integer -> k) deriving Functor

getCPUTime :: Members '[GetCPUTime] sig => Prog sig Integer
getCPUTime = call (Alg (GetCPUTime return))

algIO :: Algebra [GetLine, PutStrLn, GetCPUTime] IO
algIO eff
  | Just (Alg (GetLine k))    <- prj eff =
      do str <- Prelude.getLine
         return (k str)
  | Just (Alg (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k
  | Just (Alg (GetCPUTime k)) <- prj eff =
      do time <- System.CPUTime.getCPUTime
         return (k time)

algPutStrLn :: Effs '[PutStrLn] IO a -> IO a
algPutStrLn eff
  | Just (Alg (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k

evalIO :: Prog [GetLine, PutStrLn, GetCPUTime] a -> IO a
evalIO = eval algIO

handleIO
  :: forall effs oeffs t f a xeffs
  . ( Injects oeffs xeffs
    , Injects (xeffs :\\ effs) xeffs
    , Functor f
    , Forwards xeffs t
    , forall m . Monad m => Monad (t m)
    , xeffs ~ '[GetLine, PutStrLn, GetCPUTime]
    , KnownNat (Length effs))
  => Handler effs oeffs t f
  -> Prog (effs `Union` xeffs) a -> IO (Apply f a)
handleIO = handleM algIO
