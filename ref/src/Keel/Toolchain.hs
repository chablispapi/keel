-- | External tools: for the RISC-V target, an LLVM clang that can assemble RISC-V, ld.lld, and
-- QEMU (Apple's clang only targets ARM and x86, so these come from Homebrew: @brew install llvm
-- lld qemu@); for native builds, the system cc, with that LLVM clang as the assembler when it
-- is there.
module Keel.Toolchain (RiscVTools (..), findRiscVTools, buildRiscV, runQemu, qemuFor, qemuArgs, buildNative) where

import Control.Monad (filterM)
import Keel.RiscV (Board, boardXlen, linkerScript)
import Control.Exception (IOException, catch)
import System.Directory (doesFileExist, findExecutable, removeFile)
import System.Exit (ExitCode (..))
import System.FilePath ((<.>))
import System.Process (readProcessWithExitCode)

-- | toolQemu boots RV64 images, toolQemu32 RV32 ones.
data RiscVTools = RiscVTools {toolClang, toolLld, toolQemu, toolQemu32 :: FilePath}

-- | Look on PATH and in Homebrew's keg locations.
findRiscVTools :: IO (Maybe RiscVTools)
findRiscVTools = do
  clang <- llvmClang
  lld <- firstOf "ld.lld" ["/opt/homebrew/opt/lld/bin/ld.lld", "/opt/homebrew/opt/llvm/bin/ld.lld", "/opt/homebrew/bin/ld.lld"]
  qemu <- firstOf "qemu-system-riscv64" ["/opt/homebrew/bin/qemu-system-riscv64", "/usr/local/bin/qemu-system-riscv64"]
  qemu32 <- firstOf "qemu-system-riscv32" ["/opt/homebrew/bin/qemu-system-riscv32", "/usr/local/bin/qemu-system-riscv32"]
  pure (RiscVTools <$> clang <*> lld <*> qemu <*> qemu32)
  where
    firstOf name ps = do
      onPath <- findExecutable name
      maybe (firstExisting ps) (pure . Just) onPath

-- | Homebrew's LLVM clang, if it is installed.
llvmClang :: IO (Maybe FilePath)
llvmClang = firstExisting ["/opt/homebrew/opt/llvm/bin/clang", "/usr/local/opt/llvm/bin/clang"]

firstExisting :: [FilePath] -> IO (Maybe FilePath)
firstExisting ps = do
  found <- filterM doesFileExist ps
  pure (case found of
    p : _ -> Just p
    [] -> Nothing)

-- | Assemble and link a native (macOS) program: @s@ → @out@, with debug information if asked.
-- Homebrew's LLVM clang assembles about 3× faster than Apple's (spec/perf.md), so it does when
-- it is installed; cc links either way (the SDK, dsymutil for -g). The error output on failure.
buildNative :: Bool -> FilePath -> FilePath -> IO (Either String ())
buildNative debug s out = do
  clang <- llvmClang
  let g = ["-g" | debug]
  (code, _, err) <- case clang of
    Just c -> do
      let o = out <.> "o"
      r@(c1, _, _) <- readProcessWithExitCode c (g ++ ["-c", "-o", o, s]) ""
      linked <- case c1 of
        ExitSuccess -> do
          l@(c2, _, _) <- readProcessWithExitCode "cc" ["-o", out, o] ""
          -- cc makes OUT.dSYM only when it assembled the file itself; dsymutil reads the
          -- object's debug information, so before the object goes.
          if debug && c2 == ExitSuccess then readProcessWithExitCode "dsymutil" [out] "" else pure l
        _ -> pure r
      removeFile o `catch` \(_ :: IOException) -> pure ()
      pure linked
    Nothing -> readProcessWithExitCode "cc" (g ++ ["-o", out, s]) ""
  pure (if code == ExitSuccess then Right () else Left err)

-- | Assemble and link a RISC-V program for a board: @out.s@ → @out@ (an ELF image).
buildRiscV :: RiscVTools -> Board -> FilePath -> String -> IO (Either String FilePath)
buildRiscV tools board out asm = do
  let s = out <.> "s"
      o = out <.> "o"
      ld = out <.> "ld"
      arch
        | boardXlen board == 32 = ["--target=riscv32-unknown-elf", "-march=rv32imac", "-mabi=ilp32"]
        | otherwise = ["--target=riscv64-unknown-elf", "-march=rv64imac", "-mabi=lp64"]
  writeFile s asm
  writeFile ld (linkerScript board)
  (c1, _, e1) <- readProcessWithExitCode (toolClang tools) (arch ++ ["-mno-relax", "-c", s, "-o", o]) ""
  case c1 of
    ExitFailure _ -> pure (Left ("assembler failed:\n" ++ e1))
    ExitSuccess -> do
      (c2, _, e2) <- readProcessWithExitCode (toolLld tools) ["-T", ld, o, "-o", out] ""
      pure $ case c2 of
        ExitFailure _ -> Left ("linker failed:\n" ++ e2)
        ExitSuccess -> Right out

-- | Boot the image on QEMU's virt board with @input@ typed into the UART; the UART is stdout.
-- Returns the exit status (from the board's test device) and the output.
runQemu :: RiscVTools -> Int -> FilePath -> String -> IO (ExitCode, String)
runQemu tools xlen elf input = do
  (code, out, _) <- readProcessWithExitCode (qemuFor tools xlen) (qemuArgs elf) input
  pure (code, out)

-- | The QEMU for RV64 or RV32 images.
qemuFor :: RiscVTools -> Int -> FilePath
qemuFor tools xlen = if xlen == 32 then toolQemu32 tools else toolQemu tools

-- | QEMU's arguments for the image: the virt board, the UART on stdin and stdout.
qemuArgs :: FilePath -> [String]
qemuArgs elf = ["-machine", "virt", "-m", "256M", "-nographic", "-bios", "none", "-kernel", elf]
