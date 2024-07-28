{-# LANGUAGE CPP #-}

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Program
import Distribution.Simple.Utils
import Distribution.PackageDescription

main = defaultMainWithHooks hooks
  where
    hooks = simpleUserHooks {
#if __GLASGOW_HASKELL__ >= 910
      hookedPreProcessors = [(Suffix "md", ppMarkdownUnlit)]
#else
      hookedPreProcessors = [("md", ppMarkdownUnlit)]
#endif
    }

ppMarkdownUnlit  :: BuildInfo -> LocalBuildInfo -> ComponentLocalBuildInfo -> PreProcessor
ppMarkdownUnlit _bi lbi clbi =
  PreProcessor {
    platformIndependent = False,
    ppOrdering = unsorted,
    runPreProcessor = mkSimplePreProcessor $ \inFile outFile verbosity -> do
      do info verbosity $ "Running markdown-unlit on " ++ inFile ++ " to create " ++ outFile
      (prog, _) <- requireProgram verbosity markdownUnlitProgram (withPrograms lbi)
      runProgram verbosity prog $ "-h" : inFile : inFile : outFile : []
      return ()
  }

markdownUnlitProgram :: Program
markdownUnlitProgram = (simpleProgram "markdown-unlit")
