{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Effect.IO where

import Data.HFunctor.HComposes
import qualified System.CPUTime
import Control.Effect
import Data.List.Kind
import Data.Functor.Composes
import Control.Family

import Control.Family.Algebraic

type GetLine = Alg GetLine'
data GetLine' k  = GetLine (String -> k) deriving Functor

getLine :: Members '[GetLine] sig => Prog sig String
getLine = injCall (Alg (GetLine return))


type PutStrLn = Alg PutStrLn'
data PutStrLn' k = PutStrLn String k     deriving Functor

putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = injCall (Alg (PutStrLn str (return ())))

type GetCPUTime = Alg (GetCPUTime')
data GetCPUTime' k = GetCPUTime (Integer -> k) deriving Functor

getCPUTime :: Members '[GetCPUTime] sig => Prog sig Integer
getCPUTime = injCall (Alg (GetCPUTime return))

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
  :: forall ieffs oeffs ts fs a xeffs
  . ( Injects oeffs xeffs
    , Injects (xeffs :\\ ieffs) xeffs
    , Functors fs
    , Forwards xeffs ts
    , forall m . Monad m => Monad (HComps ts m)
    , xeffs ~ '[GetLine, PutStrLn, GetCPUTime]
    , KnownNat (Length ieffs))
  => Handler ieffs oeffs ts fs
  -> Prog (ieffs `Union` xeffs) a -> IO (RComposes fs a)
handleIO = handleM algIO

