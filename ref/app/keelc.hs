-- | keelc: the Keel compiler driver.
--
-- > keelc check FILE.kl          type-check, print main's type and effects
-- > keelc run   FILE.kl          run with the reference evaluator
-- > keelc asm   FILE.kl          print the ARM64 assembly
-- > keelc build FILE.kl [-o OUT] compile to a native executable (via the system cc)
module Main (main) where

import Keel.AArch64 (compileNative)
import Keel.Check (TypeError (..), checkProgram)
import Keel.Eval (Outcome (..), evalProgram)
import Keel.Infer (inferProgram)
import Keel.Mono (compile)
import Keel.Parser (parseProgram)
import Keel.Syntax (Program, prettyEff, prettyTy)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (dropExtension, (<.>))
import System.IO (hPutStr, hPutStrLn, stderr)
import System.Process (readProcessWithExitCode)

usage :: String
usage = "usage: keelc (check | run | asm | build [-o OUT]) FILE.kl"

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["check", f] -> do
      core <- load f
      mono <- orDie (showErr (compile core))
      (t, eff) <- orDie (showErr (checkProgram mono))
      putStrLn ("ok: main : " ++ prettyTy t ++ (if null (prettyEff eff) then "" else " ! " ++ prettyEff eff))
    ["run", f] -> do
      core <- load f
      mono <- orDie (showErr (compile core))
      let (outcome, trace) = evalProgram mono
      mapM_ print trace
      case outcome of
        Done v -> putStrLn ("result: " ++ show v)
        Panicked msg -> hPutStrLn stderr ("panic: " ++ msg) >> exitWith (ExitFailure 101)
    ["asm", f] -> do
      core <- load f
      putStr =<< orDie (compileNative core)
    "build" : rest -> case rest of
      [f] -> build f (dropExtension f)
      [f, "-o", out] -> build f out
      ["-o", out, f] -> build f out
      _ -> die usage
    _ -> die usage

-- | Parse and infer: the λK₃ program the core pipeline takes.
load :: FilePath -> IO Program
load f = do
  src <- readFile f
  surface <- orDie (parseProgram f src)
  orDie (showErr (inferProgram surface))

build :: FilePath -> FilePath -> IO ()
build f out = do
  core <- load f
  asm <- orDie (compileNative core)
  let s = out <.> "s"
  writeFile s asm
  (code, _, err) <- readProcessWithExitCode "cc" ["-o", out, s] ""
  case code of
    ExitSuccess -> putStrLn ("built " ++ out)
    ExitFailure _ -> hPutStr stderr err >> die "cc failed"

showErr :: Either TypeError a -> Either String a
showErr = either (\(TypeError k msg) -> Left ("error [" ++ show k ++ "]: " ++ msg)) Right

orDie :: Either String a -> IO a
orDie = either die pure

die :: String -> IO a
die msg = hPutStrLn stderr msg >> exitWith (ExitFailure 1)
