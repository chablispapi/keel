-- | External tools for the RISC-V target: an LLVM clang that can assemble RISC-V, ld.lld, and
-- QEMU. Apple's clang only targets ARM and x86, so these come from Homebrew
-- (@brew install llvm lld qemu@).
module Keel.Toolchain (RiscVTools (..), findRiscVTools, buildRiscV, runQemu) where

import Control.Monad (filterM)
import Keel.RiscV (linkerScript)
import System.Directory (doesFileExist, findExecutable)
import System.Exit (ExitCode (..))
import System.FilePath ((<.>))
import System.Process (readProcessWithExitCode)

data RiscVTools = RiscVTools {toolClang, toolLld, toolQemu :: FilePath}

-- | Look on PATH and in Homebrew's keg locations.
findRiscVTools :: IO (Maybe RiscVTools)
findRiscVTools = do
  clang <- firstExisting ["/opt/homebrew/opt/llvm/bin/clang", "/usr/local/opt/llvm/bin/clang"]
  lld <- firstOf "ld.lld" ["/opt/homebrew/opt/lld/bin/ld.lld", "/opt/homebrew/opt/llvm/bin/ld.lld", "/opt/homebrew/bin/ld.lld"]
  qemu <- firstOf "qemu-system-riscv64" ["/opt/homebrew/bin/qemu-system-riscv64", "/usr/local/bin/qemu-system-riscv64"]
  pure (RiscVTools <$> clang <*> lld <*> qemu)
  where
    firstExisting ps = do
      found <- filterM doesFileExist ps
      pure (case found of
        p : _ -> Just p
        [] -> Nothing)
    firstOf name ps = do
      onPath <- findExecutable name
      maybe (firstExisting ps) (pure . Just) onPath

-- | Assemble and link a RISC-V program: @out.s@ → @out@ (an ELF image for QEMU's virt board).
buildRiscV :: RiscVTools -> FilePath -> String -> IO (Either String FilePath)
buildRiscV tools out asm = do
  let s = out <.> "s"
      o = out <.> "o"
      ld = out <.> "ld"
  writeFile s asm
  writeFile ld linkerScript
  (c1, _, e1) <- readProcessWithExitCode (toolClang tools) ["--target=riscv64-unknown-elf", "-march=rv64imac", "-mabi=lp64", "-mno-relax", "-c", s, "-o", o] ""
  case c1 of
    ExitFailure _ -> pure (Left ("assembler failed:\n" ++ e1))
    ExitSuccess -> do
      (c2, _, e2) <- readProcessWithExitCode (toolLld tools) ["-T", ld, o, "-o", out] ""
      pure $ case c2 of
        ExitFailure _ -> Left ("linker failed:\n" ++ e2)
        ExitSuccess -> Right out

-- | Boot the image on QEMU's virt board; the UART is stdout. Returns the exit status (from
-- the board's test device) and the output.
runQemu :: RiscVTools -> FilePath -> IO (ExitCode, String)
runQemu tools elf = do
  (code, out, _) <-
    readProcessWithExitCode
      (toolQemu tools)
      ["-machine", "virt", "-m", "256M", "-nographic", "-bios", "none", "-kernel", elf]
      ""
  pure (code, out)
