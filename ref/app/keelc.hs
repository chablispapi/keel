-- | keelc: the Keel compiler driver and build tool.
--
-- > keelc new NAME                 create a project: NAME/keel.project, NAME/src/main.kl
-- > keelc check [FILE.kl]          type-check, print main's type and effects
-- > keelc run   [FILE.kl]          run with the reference evaluator
-- > keelc asm   [FILE.kl] [-g]     print the ARM64 assembly
-- > keelc build [FILE.kl] [-o OUT] [--target native|riscv64] [-g]
-- >                                compile (native: via the system cc; riscv64: a freestanding
-- >                                image for QEMU's virt board); -g adds debug info (native)
-- > keelc qemu  [FILE.kl]          build for RISC-V and boot it in QEMU
-- > keelc lsp                      the language server, over stdin/stdout ("Keel.Lsp")
--
-- Without a file, the commands use the project in the current directory (keel.project): its
-- entry file, its target, and build/NAME as the output. A file's imports are loaded relative
-- to its directory ("Keel.Modules").
module Main (main) where

import Data.Char (isSpace)
import Data.Map.Strict qualified as M
import Keel.AArch64 (compileNativeWith)
import Keel.Check (TypeError (..), checkProgram)
import Control.Exception (IOException, try)
import Data.ByteString qualified as B
import Data.ByteString.Char8 qualified as BC
import Keel.Eval (Machine (..), Outcome (..), evalProgramOn)
import System.IO.Unsafe (unsafePerformIO)
import Keel.Infer (inferProgram)
import Keel.Lsp (serve)
import Keel.Modules (loadModules)
import Keel.Mono (compile)
import Keel.RiscV (compileRiscV)
import Keel.Syntax (Program, prettyEff, prettyTy)
import Keel.Toolchain (RiscVTools, buildRiscV, findRiscVTools, runQemu)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, makeAbsolute)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (dropExtension, takeDirectory, (<.>), (</>))
import System.IO (hPutStr, hPutStrLn, hSetBinaryMode, stderr, stdin, stdout)
import System.Process (readProcessWithExitCode)

usage :: String
usage =
  unlines
    [ "usage: keelc new NAME"
    , "       keelc (check | run | asm | qemu) [FILE.kl]"
    , "       keelc build [FILE.kl] [-o OUT] [--target native|riscv64] [-g]"
    , "       keelc lsp"
    , "Without FILE.kl, keelc uses keel.project in the current directory."
    ]

data Target = Native | RiscV64
  deriving (Eq)

-- | What to build: the entry file, the target, the output path, and whether to add debug info.
data Job = Job {jobEntry :: FilePath, jobTarget :: Target, jobOut :: FilePath, jobDebug :: Bool}

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["new", name] -> newProject name
    ["lsp"] -> serve stdin stdout
    cmd : rest | cmd `elem` ["check", "run", "asm", "qemu", "build"] -> do
      job <- jobFor rest
      case cmd of
        "check" -> do
          (sources, core) <- load (jobEntry job)
          mono <- orDie (showErr sources (compile core))
          (t, eff) <- orDie (showErr sources (checkProgram mono))
          putStrLn ("ok: main : " ++ prettyTy t ++ (if null (prettyEff eff) then "" else " ! " ++ prettyEff eff))
        "run" -> do
          (sources, core) <- load (jobEntry job)
          mono <- orDie (showErr sources (compile core))
          -- getc reads stdin's bytes, lazily: a program that reads nothing doesn't wait for input.
          -- putc writes bytes.
          hSetBinaryMode stdin True
          hSetBinaryMode stdout True
          input <- getContents
          let (outcome, output) = evalProgramOn (Machine input readBytes) mono
          putStr output
          case outcome of
            Done v -> putStrLn ("result: " ++ show v)
            Panicked msg -> hPutStrLn stderr ("panic: " ++ msg) >> exitWith (ExitFailure 101)
        "asm" -> do
          (_, core) <- load (jobEntry job)
          putStr =<< orDie (compileNativeWith (jobDebug job) core)
        "qemu" -> do
          (tools, elf) <- buildRv (jobEntry job) (jobOut job)
          (code, out) <- runQemu tools elf
          putStr out
          exitWith code
        _ -> case jobTarget job of
          Native -> build job
          RiscV64 -> () <$ buildRv (jobEntry job) (jobOut job)
    _ -> die usage

-- | Arguments after the command: an optional file, -o OUT, --target T. Without a file, the
-- project in the current directory provides the defaults.
jobFor :: [String] -> IO Job
jobFor args = do
  let (file, out, target) = parseArgs (filter (/= "-g") args) (Nothing, Nothing, Nothing)
  base <- case file of
    Just f -> pure (Job f Native (dropExtension f) ("-g" `elem` args))
    Nothing -> do
      hasProject <- doesFileExist "keel.project"
      if not hasProject
        then die ("no FILE.kl given and no keel.project here\n" ++ usage)
        else do
          m <- readManifest "keel.project"
          let name = M.findWithDefault "main" "name" m
              target' = if M.lookup "target" m == Just "riscv64" then RiscV64 else Native
          pure (Job (M.findWithDefault "src/main.kl" "main" m) target' ("build" </> name) ("-g" `elem` args))
  t <- case target of
    Nothing -> pure (jobTarget base)
    Just "native" -> pure Native
    Just "riscv64" -> pure RiscV64
    Just other -> die ("unknown target " ++ other ++ " (native or riscv64)")
  let job = base {jobTarget = t, jobOut = maybe (jobOut base) id out}
  createDirectoryIfMissing True (takeDirectory (jobOut job))
  pure job
  where
    parseArgs as acc@(f, o, t) = case as of
      [] -> acc
      "-o" : x : rest -> parseArgs rest (f, Just x, t)
      "--target" : x : rest -> parseArgs rest (f, o, Just x)
      x : rest -> parseArgs rest (Just x, o, t)

-- | keel.project: @key = value@ lines; @#@ starts a comment.
readManifest :: FilePath -> IO (M.Map String String)
readManifest path = do
  src <- readFile path
  pure $
    M.fromList
      [ (trim k, trim (drop 1 v))
      | l <- lines src
      , let l' = takeWhile (/= '#') l
      , let (k, v) = break (== '=') l'
      , not (null v)
      ]
  where
    trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

newProject :: String -> IO ()
newProject name = do
  exists <- doesDirectoryExist name
  if exists
    then die (name ++ " already exists")
    else do
      createDirectoryIfMissing True (name </> "src")
      writeFile (name </> "keel.project") (unlines ["name = " ++ name, "main = src/main.kl", "# native, or riscv64 for QEMU's virt board", "target = native"])
      writeFile (name </> "src" </> "main.kl") (unlines ["-- " ++ name, "", "main = println \"Hello from " ++ name ++ "!\""])
      writeFile (name </> ".gitignore") "build/\n"
      putStrLn ("created " ++ name ++ "/ (keel.project, src/main.kl); cd " ++ name ++ " && keelc run")

-- | Load the entry file with its imports, and infer: the sources (for error messages) and the
-- λK₃ program the core pipeline takes. Core errors are reported here too, with positions.
load :: FilePath -> IO (M.Map FilePath String, Program)
load f = do
  (surface, sources) <- orDie =<< loadModules f
  core <- orDie (showErr sources (inferProgram surface))
  _ <- orDie (showErr sources (compile core))
  pure (sources, core)

-- | With -g, cc turns the line table into DWARF and runs dsymutil (OUT.dSYM), so lldb can
-- break on and step through .kl lines.
build :: Job -> IO ()
build job = do
  let out = jobOut job
  -- Debug info names files by absolute path, so lldb finds them from anywhere.
  entry <- if jobDebug job then makeAbsolute (jobEntry job) else pure (jobEntry job)
  (_, core) <- load entry
  asm <- orDie (compileNativeWith (jobDebug job) core)
  let s = out <.> "s"
  writeFile s asm
  (code, _, err) <- readProcessWithExitCode "cc" (["-g" | jobDebug job] ++ ["-o", out, s]) ""
  case code of
    ExitSuccess -> putStrLn ("built " ++ out)
    ExitFailure _ -> hPutStr stderr err >> die "cc failed"

buildRv :: FilePath -> FilePath -> IO (RiscVTools, FilePath)
buildRv f out = do
  (_, core) <- load f
  asm <- orDie (compileRiscV core)
  tools <- maybe (die "RISC-V needs Homebrew's llvm, lld and qemu: brew install llvm lld qemu") pure =<< findRiscVTools
  elf <- orDie =<< buildRiscV tools out asm
  hPutStrLn stderr ("built " ++ elf ++ " (RISC-V, QEMU virt)")
  pure (tools, elf)

-- | @file:line:col: error [Kind]: message@, then the source line with a caret under the column.
showErr :: M.Map FilePath String -> Either TypeError a -> Either String a
showErr sources = either (Left . render) Right
  where
    render (TypeError k msg pos) = case pos of
      Nothing -> "error [" ++ show k ++ "]: " ++ msg
      Just (f, l, c) ->
        let srcLine = case drop (l - 1) (lines (M.findWithDefault "" f sources)) of
              s : _ -> s
              [] -> ""
            gutter = show l ++ " | "
         in f ++ ":" ++ show l ++ ":" ++ show c ++ ": error [" ++ show k ++ "]: " ++ msg ++ "\n"
              ++ gutter ++ srcLine ++ "\n"
              ++ replicate (length gutter + c - 1) ' ' ++ "^"

-- | The files keelc run's programs can open, read when they open them.
-- ponytail: unsafePerformIO keeps the evaluator pure; a file changed while the program runs is
-- read as it is when opened, which is what fopen gives too.
readBytes :: FilePath -> Maybe String
readBytes path = unsafePerformIO $ do
  r <- try (B.readFile path)
  pure (either (\(_ :: IOException) -> Nothing) (Just . BC.unpack) r)
{-# NOINLINE readBytes #-}

orDie :: Either String a -> IO a
orDie = either die pure

die :: String -> IO a
die msg = hPutStrLn stderr msg >> exitWith (ExitFailure 1)
