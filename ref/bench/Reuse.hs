-- Emit paired assemblies from one compiler; only constructor-reuse specialization differs.
module Main (main) where

import Control.Monad (forM_)
import Keel.AArch64 (compileNativeWithReuse)
import Keel.Infer (inferProgram)
import Keel.Modules (loadModules)
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [source, prefix] -> do
      loaded <- loadModules source >>= either fail pure
      program <- either (fail . show) pure (inferProgram (fst loaded))
      forM_ [("baseline", False), ("candidate", True)] $ \(name, enabled) -> do
        asm <- either fail pure (compileNativeWithReuse False enabled program)
        writeFile (prefix ++ "." ++ name ++ ".s") asm
    _ -> fail "usage: reuse-emit SOURCE OUTPUT_PREFIX"
