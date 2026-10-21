-- | Runs the examples of spec/core.md (test/Cases.hs) through the reference pipeline.
module Main (main) where

import Cases
import Control.Monad (unless)
import Keel.Check
import Keel.Elab
import Keel.Eval
import Keel.Mono
import System.Exit (exitFailure)

-- Runner --------------------------------------------------------------------------------

main :: IO ()
main = do
  let failures = concatMap run cases
  mapM_ putStrLn failures
  putStrLn (show (length cases - length failures) ++ "/" ++ show (length cases) ++ " passed")
  unless (null failures) exitFailure
  where
    run (name, prog, expect) = case (compile prog, expect) of
      (Left (TypeError k _), Rejects k') -> [failMsg name ("expected " ++ show k' ++ ", got " ++ show k) | k /= k']
      (Left e, _) -> [failMsg name ("unexpected rejection: " ++ show e)]
      (Right t, Rejects k) -> [failMsg name ("expected " ++ show k ++ ", but accepted at " ++ show t)]
      (Right mono, _) ->
        let got = evalProgram (elaborate prog)
         in [failMsg name "monomorphized program still has type variables" | not (isClosed mono)]
              ++ [failMsg name ("monomorphization changed the result: " ++ show (evalProgram mono)) | evalProgram mono /= got]
              ++ case (got, expect) of
                ((Done v, tr), Gives v' tr') | v == v' && tr == tr' -> []
                ((Panicked _, tr), Panics tr') | tr == tr' -> []
                _ -> [failMsg name ("got " ++ show got)]
    failMsg name msg = "FAIL " ++ name ++ ": " ++ msg
