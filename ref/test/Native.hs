-- | Native differential tests: each program is compiled to ARM64 assembly, linked with the
-- system @cc@ and run. Its output must match the reference evaluator: same @out@ trace, and
-- the same result (last line @result: …@, printed like the evaluator) or a panic (exit 101).
--
-- Programs: every accepted example of spec/core.md (test/Cases.hs), back-end tests below, and
-- the example files (examples/*.kl), which also have hand-written expected output.
module Main (main) where

import Cases (Expect (..))
import Cases qualified
import Control.Monad (forM, unless)
import Data.List (isInfixOf, stripPrefix)
import Data.Set qualified as S
import Keel.AArch64 (compileNative)
import Keel.Eval (Outcome (..), evalProgram)
import Keel.Infer (inferProgram)
import Keel.Parser (parseProgram)
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

-- def loop : i64 → i64 →{Panic, Diverge} i64, tail recursive with an accumulator
loopDef :: Decl
loopDef =
  Def "loop" (fn tI (fnE [panicE, divergeE] tI tI)) $
    Lam "i" tI $
      Lam "acc" tI (If (lt (Var "i") (int 1)) (Var "acc") (App (App (Var "loop") (sub (Var "i") (int 1))) (add (Var "acc") (Var "i"))))

u64Max :: Integer
u64Max = 18446744073709551615

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
  , ("tail calls run in constant stack", Program [loopDef] (App (App (Var "loop") (int 3000000)) (int 0)))
  , ("u64 wrapping add", Program [] (Prim (Arith Wrap Add) (IntLit u64 u64Max) (IntLit u64 2)))
  , ("u64 checked add overflows", Program [] (Prim (Arith Checked Add) (IntLit u64 u64Max) (IntLit u64 1)))
  , ("u64 saturating sub", Program [] (Prim (Arith Saturate Sub) (IntLit u64 3) (IntLit u64 5)))
  , ("u64 saturating mul", Program [] (Prim (Arith Saturate Mul) (IntLit u64 u64Max) (IntLit u64 2)))
  , ("u64 compare is unsigned", Program [] (Prim Lt (IntLit u64 1) (IntLit u64 u64Max)))
  , ("i64 saturating mul, negative", Program [] (Prim (Arith Saturate Mul) (int (-4611686018427387904)) (int 3)))
  , ("i32 checked mul overflows", Program [] (Prim (Arith Checked Mul) (IntLit i32 65536) (IntLit i32 65536)))
  , ("u32 saturating mul", Program [] (Prim (Arith Saturate Mul) (IntLit u32 4000000000) (IntLit u32 4000000000)))
  , ("u16 +? overflow", Program [] (Prim (Arith Optional Add) (IntLit u16 65535) (IntLit u16 1)))
  , ("i16 wrapping sub", Program [] (Prim (Arith Wrap Sub) (IntLit i16 (-32768)) (IntLit i16 1)))
  ]

-- | Programs M0 must refuse cleanly.
unsupportedCases :: [(String, Program)]
unsupportedCases =
  [("effect handlers (M3)", Program [] (Handle ioE (Perform "out" (int 5)) [("out", "x", UnitLit)]))]

-- | Accepted spec examples; those using handlers are skipped until M3.
specCases :: [(String, Program)]
specCases = [("spec: " ++ name, p) | (name, p, e) <- Cases.cases, runs e, not (usesHandlers p)]
  where
    runs (Rejects _) = False
    runs _ = True

usesHandlers :: Program -> Bool
usesHandlers (Program _ m) = any isHandle (universe m)
  where
    isHandle Handle {} = True
    isHandle _ = False

-- | Example files and what they must print: (result, or Nothing for a panic; out trace).
exampleFiles :: [(FilePath, Run)]
exampleFiles =
  [ ("examples/hello.kl", (Just "25", [9, 16]))
  , ("examples/fact.kl", (Just "500000500000", [2432902008176640000]))
  , ("examples/lists.kl", (Just "60", []))
  , ("examples/sort.kl", (Just "Cons(3, box Cons(2, box Cons(1, box Nil)))", []))
  , ("examples/counter.kl", (Just "44", []))
  , ("examples/uart.kl", (Just "()", [72, 105]))
  , ("examples/overflow.kl", (Nothing, [1, 2]))
  , ("examples/widths.kl", (Just "(4, (255, (None, Some(3))))", []))
  ]

-- | Parse and infer an example; check the evaluator against the expected output, and return
-- the program for the native comparison unless it uses handlers.
loadExample :: (FilePath, Run) -> IO ([String], [(String, Program)])
loadExample (path, expected) = do
  src <- readFile path
  case parseProgram path src >>= either (Left . show) Right . inferProgram of
    Left e -> pure (["FAIL " ++ path ++ ": " ++ e], [])
    Right core -> case compile core of
      Left e -> pure (["FAIL " ++ path ++ ": " ++ show e], [])
      Right mono -> do
        let got = reduce (evalProgram mono)
            fails = ["FAIL " ++ path ++ ": evaluator gave " ++ show got ++ ", expected " ++ show expected | got /= expected]
        pure (fails, [(path, core) | not (usesHandlers core)])

main :: IO ()
main = do
  dir <- (</> "keel-native-tests") <$> getTemporaryDirectory
  createDirectoryIfMissing True dir
  loaded <- mapM loadExample exampleFiles
  let programs = cases ++ specCases ++ concatMap snd loaded
  failures <- (concatMap fst loaded ++) . concat <$> forM (zip [0 :: Int ..] programs) (uncurry (runCase dir))
  let refused =
        [ "FAIL " ++ name ++ ": expected 'not supported yet', got " ++ either id (const "assembly") r
        | (name, p) <- unsupportedCases
        , let r = compileNative p
        , either (not . ("not supported yet" `isInfixOf`)) (const True) r
        ]
      allFailures = failures ++ refused
      total = length programs + length unsupportedCases + length exampleFiles
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
