import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PreProcess
import Distribution.Simple.Program
import Distribution.Simple.Utils
import Distribution.PackageDescription

main = defaultMainWithHooks hooks
  where
    hooks = simpleUserHooks {
      hookedPreProcessors = [("md", ppMarkdownUnlit)]
    }

ppMarkdownUnlit  :: BuildInfo -> LocalBuildInfo -> ComponentLocalBuildInfo -> PreProcessor
ppMarkdownUnlit _bi lbi clbi =
  PreProcessor {
    platformIndependent = False,
    ppChoosedering = unsorted,
    runPreProcessor = mkSimplePreProcessor $ \inFile outFile verbosity -> do
      do info verbosity $ "Running markdown-unlit on " ++ inFile ++ " to create " ++ outFile
      (prog, _) <- requireProgram verbosity markdownUnlitProgram (withPrograms lbi)
      runProgram verbosity prog $ "-h" : inFile : inFile : outFile : []
      return ()
  }

markdownUnlitProgram :: Program
markdownUnlitProgram = (simpleProgram "markdown-unlit")
