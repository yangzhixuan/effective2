{-# LANGUAGE DataKinds #-}

module Control.Effect.IO where

import qualified System.CPUTime
import Control.Effect
import Data.List.Kind
import Data.Functor.Composes

data GetLine k  = GetLine (String -> k) deriving Functor

getLine :: Members '[GetLine] sig => Prog sig String
getLine = injCall (Alg (GetLine return))


data PutStrLn k = PutStrLn String k     deriving Functor

putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = injCall (Alg (PutStrLn str (return ())))

data GetCPUTime k = GetCPUTime (Integer -> k) deriving Functor

getCPUTime :: Members '[GetCPUTime] sig => Prog sig Integer
getCPUTime = injCall (Alg (GetCPUTime return))


algIO :: Effs [GetLine, PutStrLn, GetCPUTime] IO a -> IO a
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
  :: forall ieffs oeffs fs a xeffs
  . ( Append ieffs (xeffs :\\ ieffs)
    , Injects oeffs xeffs
    , Injects (xeffs :\\ ieffs) xeffs
    , Recompose fs
    , xeffs ~ '[GetLine, PutStrLn, GetCPUTime] )
  => Handler ieffs oeffs fs
  -> Prog (ieffs `Union` xeffs) a -> IO (Composes fs a)
handleIO = handleWith algIO

