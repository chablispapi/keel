-- | M0 differential tests: each program is compiled to ARM64 assembly, linked with the system
-- @cc@ and run. Its output must match the reference evaluator: same @out@ trace, and the same
-- result (last line @result: …@) or a panic (exit status 101).
module Main (main) where

import Control.Monad (forM, unless)
import Data.List (isInfixOf, stripPrefix)
import Data.Set qualified as S
import Keel.AArch64 (compileNative)
import Keel.Eval (Outcome (..), evalProgram)
import Keel.Mono (compile)
import Keel.Syntax
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

tI :: Ty
tI = TInt i64

int :: Integer -> Term
int = IntLit i64

fn :: Ty -> Ty -> Ty
fn a = TFun a S.empty

fnE :: [String] -> Ty -> Ty -> Ty
fnE es a = TFun a (S.fromList es)

add, sub, mul, lt, eq :: Term -> Term -> Term
add = Prim (Arith Checked Add)
sub = Prim (Arith Checked Sub)
mul = Prim (Arith Checked Mul)
lt = Prim Lt
eq = Prim Eq

out :: Term -> Term
out = Perform "out"

-- def fact : i64 →{Panic, Diverge} i64 = λn. if n < 1 then 1 else n * fact (n - 1)
factDef :: Decl
factDef =
  Def "fact" (fnE [panicE, divergeE] tI tI) $
    Lam "n" tI (If (lt (Var "n") (int 1)) (int 1) (mul (Var "n") (App (Var "fact") (sub (Var "n") (int 1)))))

-- def fib : i64 →{Panic, Diverge} i64
fibDef :: Decl
fibDef =
  Def "fib" (fnE [panicE, divergeE] tI tI) $
    Lam "k" tI (If (lt (Var "k") (int 2)) (Var "k") (add (App (Var "fib") (sub (Var "k") (int 1))) (App (Var "fib") (sub (Var "k") (int 2)))))

-- def twice : (i64 →{Panic} i64) → i64 →{Panic} i64 = λf. λx. f (f x)
twiceDef :: Decl
twiceDef =
  Def "twice" (fn (fnE [panicE] tI tI) (fnE [panicE] tI tI)) $
    Lam "f" (fnE [panicE] tI tI) (Lam "x" tI (App (Var "f") (App (Var "f") (Var "x"))))

-- Mutual recursion with wrapping subtraction (no Panic).
evenOdd :: [Decl]
evenOdd =
  [ Def "isEven" (fnE [divergeE] tI TBool) (Lam "a" tI (If (eq (Var "a") (int 0)) (BoolLit True) (App (Var "isOdd") (Prim (Arith Wrap Sub) (Var "a") (int 1)))))
  , Def "isOdd" (fnE [divergeE] tI TBool) (Lam "b" tI (If (eq (Var "b") (int 0)) (BoolLit False) (App (Var "isEven") (Prim (Arith Wrap Sub) (Var "b") (int 1)))))
  ]

-- Polymorphic definitions, specialized by monomorphization before code generation.
polyDefs :: [Decl]
polyDefs =
  [ Def "id" (TForall [("a", Lin)] [] (fn (TVar "a") (TVar "a"))) (Lam "x" (TVar "a") (Var "x"))
  , Def "twice2" (TForall [("b", Lin)] [] (fn (TVar "b") (TVar "b"))) $
      Lam "y" (TVar "b") (App (TyApp "id" [TVar "b"] []) (App (TyApp "id" [TVar "b"] []) (Var "y")))
  ]

sumToDef :: Decl
sumToDef =
  Def "sumTo" (fnE [panicE, divergeE] tI tI) $
    Lam "m" tI (If (lt (Var "m") (int 1)) (int 0) (add (Var "m") (App (Var "sumTo") (sub (Var "m") (int 1)))))

adderDef :: Decl
adderDef = Def "adder" (fn tI (fnE [panicE] tI tI)) (Lam "p" tI (Lam "q" tI (add (Var "p") (Var "q"))))

cases :: [(String, Program)]
cases =
  [ ("arithmetic", Program [] (Let "x" (int 6) (mul (Var "x") (int 7))))
  , ("if", Program [] (If (lt (int 3) (int 5)) (int 1) (int 2)))
  , ( "closure capturing a variable"
    , Program [] (Let "addc" (Lam "a" tI (Lam "b" tI (add (Var "a") (Var "b")))) (Let "add5" (App (Var "addc") (int 5)) (App (Var "add5") (int 10))))
    )
  , ("higher-order function", Program [twiceDef] (App (App (Var "twice") (Lam "n" tI (mul (Var "n") (int 3)))) (int 2)))
  , ("recursion: fact 20", Program [factDef] (App (Var "fact") (int 20)))
  , ("recursion: fib 20", Program [fibDef] (App (Var "fib") (int 20)))
  , ("out trace", Program [] (Seq (out (int 1)) (Seq (out (int 2)) (int 3))))
  , ("overflow panics after output", Program [factDef] (Seq (out (int 7)) (App (Var "fact") (int 21))))
  , ( "polymorphism through monomorphization"
    , Program polyDefs (If (App (TyApp "twice2" [TBool] []) (BoolLit True)) (App (TyApp "twice2" [tI] []) (int 1)) (int 0))
    )
  , ("linear closure", Program [] (Let "k" (LLam "n" tI (add (Var "n") (int 1))) (App (Var "k") (int 41))))
  , ("Bool result", Program [] (eq (int 2) (int 2)))
  , ("large negative constant", Program [] (add (int (-5000000000)) (int 1)))
  , ("mutual recursion", Program evenOdd (App (Var "isEven") (int 10)))
  , ("wrapping overflow", Program [] (Prim (Arith Wrap Add) (int 9223372036854775807) (int 1)))
  , ( "closure capturing several values"
    , Program
        []
        ( Let "a" (int 1) . Let "b" (int 2) . Let "c" (int 3) $
            Let "g" (Lam "z" tI (add (add (add (mul (Var "a") (int 100)) (mul (Var "b") (int 10))) (Var "c")) (Var "z"))) (App (Var "g") (int 0))
        )
    )
  , ("known call returning a closure", Program [adderDef] (App (App (Var "adder") (int 40)) (int 2)))
  , ("Unit result", Program [] (out (int 5)))
  , ("deep recursion", Program [sumToDef] (App (Var "sumTo") (int 10000)))
  ]

-- | Programs M0 must refuse cleanly.
unsupportedCases :: [(String, Program)]
unsupportedCases =
  [ ( "data types (M1)"
    , Program [Data False "Two" [] [("A", []), ("B", [])]] (Case (Con "A" [] []) [("A", [], int 1), ("B", [], int 2)])
    )
  , ("narrow integers (M1)", Program [] (IntLit u8 3))
  ]

main :: IO ()
main = do
  dir <- (</> "keel-native-tests") <$> getTemporaryDirectory
  createDirectoryIfMissing True dir
  failures <- concat <$> forM (zip [0 :: Int ..] cases) (uncurry (runCase dir))
  let refused =
        [ "FAIL " ++ name ++ ": expected 'not supported in M0', got " ++ either id (const "assembly") r
        | (name, p) <- unsupportedCases
        , let r = compileNative p
        , either (not . ("not supported in M0" `isInfixOf`)) (const True) r
        ]
      allFailures = failures ++ refused
      total = length cases + length unsupportedCases
  mapM_ putStrLn allFailures
  putStrLn (show (total - length allFailures) ++ "/" ++ show total ++ " native cases passed")
  unless (null allFailures) exitFailure

runCase :: FilePath -> Int -> (String, Program) -> IO [String]
runCase dir i (name, prog) = case (compile prog, compileNative prog) of
  (Left e, _) -> pure [failMsg ("does not type-check: " ++ show e)]
  (_, Left e) -> pure [failMsg e]
  (Right mono, Right asm) -> do
    let src = dir </> ("case" ++ show i ++ ".s")
        exe = dir </> ("case" ++ show i)
    writeFile src asm
    (ccCode, _, ccErr) <- readProcessWithExitCode "cc" ["-o", exe, src] ""
    case ccCode of
      ExitFailure _ -> pure [failMsg ("cc failed:\n" ++ ccErr)]
      ExitSuccess -> do
        (code, stdout, _) <- readProcessWithExitCode exe [] ""
        let native = parseRun code (lines stdout)
            reference = reduce (evalProgram mono)
        pure [failMsg ("native " ++ show native ++ ", reference " ++ show reference) | native /= Just reference]
  where
    failMsg msg = "FAIL " ++ name ++ ": " ++ msg

-- | (result line or Nothing for a panic, out trace)
type Run = (Maybe String, [Integer])

reduce :: (Outcome, [Integer]) -> Run
reduce (Done v, tr) = (Just (show v), tr)
reduce (Panicked _, tr) = (Nothing, tr)

parseRun :: ExitCode -> [String] -> Maybe Run
parseRun code ls = case code of
  ExitSuccess | not (null ls), Just r <- stripPrefix "result: " (last ls) -> (Just r,) <$> mapM readInt (init ls)
  ExitFailure 101 -> (Nothing,) <$> mapM readInt ls
  _ -> Nothing
  where
    readInt s = case reads s of
      [(n, "")] -> Just n
      _ -> Nothing
