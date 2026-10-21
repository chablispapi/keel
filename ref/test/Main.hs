-- | Runs the examples of spec/core.md (test/Cases.hs) through the reference pipeline.
module Main (main) where

import Cases
import Control.Monad (unless)
import Keel.Check
import Keel.Elab
import Keel.Eval
import Keel.Infer (inferProgram)
import Keel.Mono
import Keel.Parser (parseProgram)
import System.Exit (exitFailure)

-- Runner --------------------------------------------------------------------------------

main :: IO ()
main = do
  let failures = concatMap run cases ++ concatMap located positionCases
      total = length cases + length positionCases
  mapM_ putStrLn failures
  putStrLn (show (total - length failures) ++ "/" ++ show total ++ " passed")
  unless (null failures) exitFailure
  where
    -- Source programs whose error must be reported with this kind at this line and column.
    located (name, src, k, pos) = case parseProgram name src of
      Left e -> [failMsg name ("parse error: " ++ e)]
      Right surface -> case inferProgram surface >>= compile of
        Left (TypeError k' _ pos')
          | k' == k && fmap (\(_, l, c) -> (l, c)) pos' == Just pos -> []
          | otherwise -> [failMsg name ("got " ++ show k' ++ " at " ++ show pos' ++ ", expected " ++ show k ++ " at " ++ show pos)]
        Right _ -> [failMsg name "accepted"]
    run (name, prog, expect) = case (compile prog, expect) of
      (Left (TypeError k _ _), Rejects k') -> [failMsg name ("expected " ++ show k' ++ ", got " ++ show k) | k /= k']
      (Left e, _) -> [failMsg name ("unexpected rejection: " ++ show e)]
      (Right t, Rejects k) -> [failMsg name ("expected " ++ show k ++ ", but accepted at " ++ show t)]
      (Right mono, _) ->
        let got = evalProgram (elaborate prog)
         in [failMsg name "monomorphized program still has type variables" | not (isClosed mono)]
              ++ [failMsg name ("monomorphization changed the result: " ++ show (evalProgram mono)) | evalProgram mono /= got]
              ++ case (got, expect) of
                ((Done v, tr), Gives v' tr') | v == v' && tr == render tr' -> []
                ((Panicked _, tr), Panics tr') | tr == render tr' -> []
                _ -> [failMsg name ("got " ++ show got)]
    failMsg name msg = "FAIL " ++ name ++ ": " ++ msg

-- | The output text of a list of @out@ values.
render :: [Integer] -> String
render = concatMap (\n -> show n ++ "\n")

positionCases :: [(String, String, ErrKind, (Int, Int))]
positionCases =
  [ ( "position: linear value used twice"
    , unlines
        [ "linear data Token = Token"
        , "def consume : Token -> i64 = \\t. case t of { Token -> 1 }"
        , "def twice : Token -> i64 ="
        , "  \\t. consume t + consume t"
        , "main = twice Token"
        ]
    , Duplicate
    , (4, 7)
    )
  , ("position: effect missing from a signature", "def inc : i64 -> i64 = \\n. n + 1\nmain = inc 41\n", EffectMismatch, (1, 24))
  , ("position: integer used as a condition", "main =\n  let x = 5 in\n  if x then 1 else 2\n", Mismatch, (3, 6))
  , ( "position: reference captured by a closure"
    , "main = var x = 1 in let g = \\u. x in g ()\n"
    , PlaceCapture
    , (1, 33)
    )
  ]
