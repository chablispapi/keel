{-# LANGUAGE LambdaCase #-}

-- | Native differential tests: each program is compiled to ARM64 assembly, linked with the
-- system @cc@ and run. Its output must match the reference evaluator: the same output text,
-- then the same result (@result: …@, printed like the evaluator) or a panic (exit 101).
-- Every run also reports its allocator counters (KEEL_STATS): a program that finishes must
-- end with no live heap blocks, so a missing drop (a leak) fails the test.
--
-- Programs: every accepted example of spec/core.md (test/Cases.hs), back-end tests below, and
-- the example files (examples/*.kl), which also have hand-written expected output.
--
-- When Homebrew's llvm, lld and qemu are installed, every program also runs on the RISC-V back
-- end, freestanding on QEMU's virt board, with the same checks; so does examples/firmware.
module Main (main) where

import Cases (Expect (..))
import Cases qualified
import Control.Monad (forM, unless)
import Data.List (isInfixOf, isPrefixOf, stripPrefix)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.AArch64 (compileNative, compileNativeWith)
import Keel.Eval (Outcome (..), evalProgram)
import Keel.Infer (inferProgram)
import Keel.Lsp (Diag (..), definition, diagnose, hover, parseJson, renderJson)
import Keel.Modules (loadModules)
import Keel.RiscV (compileRiscV)
import Keel.Toolchain (RiscVTools, buildRiscV, findRiscVTools, runQemu)
import Keel.Mono (compile)
import Keel.Syntax
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory)
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath ((</>))
import System.Process (env, proc, readCreateProcessWithExitCode, readProcessWithExitCode)

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
  , ("memory is freed: 10M pairs in a 64 MB heap", Program [churnDef] (App (App (Var "churn") (int 10000000)) (int 0)))
  , ("division truncates toward zero", Program [] (Pair (divide (int (-7)) (int 2)) (remainder (int (-7)) (int 2))))
  , ("u64 division", Program [] (Prim (Arith Checked Div) (IntLit u64 u64Max) (IntLit u64 10)))
  , ("division by zero panics", Program [] (Seq (out (int 3)) (divide (int 1) (int 0))))
  , ("i64 min / -1 panics", Program [] (divide (int (-9223372036854775808)) (int (-1))))
  , ("i64 min % -1 is 0", Program [] (remainder (int (-9223372036854775808)) (int (-1))))
  , ("i8 min / -1 panics", Program [] (Prim (Arith Checked Div) (IntLit i8 (-128)) (IntLit i8 (-1))))
  , ("u8 remainder", Program [] (Prim (Arith Checked Rem) (IntLit u8 250) (IntLit u8 7)))
  ]

divide, remainder :: Term -> Term -> Term
divide = Prim (Arith Checked Div)
remainder = Prim (Arith Checked Rem)

-- def churn : i64 → i64 →{Panic, Diverge} i64: allocates a pair per iteration and drops it.
-- 10 million pairs are ~320 MB, five times the heap: this only finishes if memory is freed.
churnDef :: Decl
churnDef =
  Def "churn" (fn tI (fnE [panicE, divergeE] tI tI)) $
    Lam "i" tI $
      Lam "acc" tI $
        If
          (lt (Var "i") (int 1))
          (Var "acc")
          ( LetPair "p" "q" (Pair (Var "i") (Var "acc")) $
              App (App (Var "churn") (sub (Var "p") (int 1))) (add (Var "q") (int 1))
          )

-- | Programs that must be refused cleanly.
unsupportedCases :: [(String, Program)]
unsupportedCases =
  [("a block with a pointer beyond word 16", Program [Data False "Big" [] [("Big", replicate 16 tI ++ [TData "Big2" []])], Data False "Big2" [] [("B2", [])]] (Con "Big" [] (replicate 16 (int 0) ++ [Con "B2" [] []])))]

-- | Accepted spec examples.
specCases :: [(String, Program)]
specCases = [("spec: " ++ name, p) | (name, p, e) <- Cases.cases, runs e]
  where
    runs (Rejects _) = False
    runs _ = True

-- | Example files and what they must print: (result, or Nothing for a panic; output text).
exampleFiles :: [(FilePath, Run)]
exampleFiles =
  [ ("examples/hello.kl", (Just "25", "9\n16\n"))
  , ("examples/fact.kl", (Just "500000500000", "2432902008176640000\n"))
  , ("examples/lists.kl", (Just "60", ""))
  , ("examples/sort.kl", (Just "Cons(3, box Cons(2, box Cons(1, box Nil)))", ""))
  , ("examples/counter.kl", (Just "44", ""))
  , ("examples/uart.kl", (Just "()", "72\n105\n"))
  , ("examples/overflow.kl", (Nothing, "1\n2\n"))
  , ("examples/widths.kl", (Just "(4, (255, (None, Some(3))))", ""))
  , ("examples/reuse.kl", (Just "1500500", ""))
  , ("examples/strings.kl", (Just "3", "Hello from Keel!\n-9223372036854775808\nhello!\nlength of abc: \n"))
  , ("examples/project/src/main.kl", (Just "100", "console ready\nled ready\nhello, modules\n42\n"))
  ]

-- | Multi-file programs the module loader must refuse, and part of the message.
moduleErrors :: [(FilePath, String)]
moduleErrors =
  [ ("test/modules/cycle/a.kl", "import cycle: a → b → a")
  , ("test/modules/dup/main.kl", "main.kl:3:8: shared is ambiguous: it is declared in x and y; write x.shared or y.shared")
  , ("test/modules/scope/hidden.kl", "hidden.kl:3:8: hidden is declared in module b; import b to use it")
  , ("test/modules/scope/private.kl", "private.kl:3:8: secret is private to module a")
  , ("test/modules/missing/main.kl", "test/modules/missing/main.kl:1:1: module nowhere not found")
  ]

-- | The language server's checks on the example project, with an unsaved edit to util.kl.
lspChecks :: IO [String]
lspChecks = do
  let util = "examples/project/src/util.kl"
  src <- readFile util
  let edit from to = M.singleton util (replaceOnce from to src)
      replaceOnce from to s = case stripPrefix from s of
        Just rest -> to ++ rest
        Nothing -> case s of c : rest -> c : replaceOnce from to rest; [] -> []
  clean <- diagnose M.empty util
  typeErr <- diagnose (edit "a + b" "a + true") util
  parseErr <- diagnose (edit "def double" "def double double") util
  h <- hover M.empty "examples/project/src/main.kl" 8 60
  let dir = "examples/project/src/"
  defs <- sequence [definition M.empty (dir ++ f) l c | (f, l, c) <- [("main.kl", 8, 32), ("main.kl", 8, 67), ("util.kl", 4, 40), ("main.kl", 6, 3)]]
  let json = "{\"a\":[1,-2.5,true,null,\"x\\n\\u00e9\"],\"b\":{}}"
  pure $
    [ "FAIL lsp: " ++ what ++ ": got " ++ got
    | (ok, what, got) <-
        [ (null clean, "clean project", show clean)
        , (typeErr == [Diag util 2 59 "expected i64, got Bool [Mismatch]"], "type error", show typeErr)
        , (case parseErr of [Diag f 4 _ _] -> f == util; _ -> False, "parse error", show parseErr)
        , (defs == map Just [(dir ++ "drivers/led.kl", 1, 5), (dir ++ "util.kl", 4, 5), (dir ++ "util.kl", 2, 13), (dir ++ "drivers/led.kl", 1, 1)], "definition", show defs)
        , (h == Just "printInt : i64 →{Diverge, IO, Panic} Unit", "hover", show h)
        , (fmap renderJson (parseJson json) == Just "{\"a\":[1,-2.5,true,null,\"x\\n\233\"],\"b\":{}}", "json", show (parseJson json))
        ]
    , not ok
    ]

checkModuleError :: (FilePath, String) -> IO [String]
checkModuleError (path, expected) =
  loadModules path >>= \case
    Left e | expected `isInfixOf` e -> pure []
    Left e -> pure ["FAIL " ++ path ++ ": got " ++ show e]
    Right _ -> pure ["FAIL " ++ path ++ ": loaded"]

-- | Parse and infer an example; check the evaluator against the expected output, and return
-- the program for the native comparison unless it uses handlers.
loadExample :: (FilePath, Run) -> IO ([String], [(String, Program)])
loadExample (path, expected) = do
  loaded <- loadModules path
  case loaded >>= either (Left . show) Right . inferProgram . fst of
    Left e -> pure (["FAIL " ++ path ++ ": " ++ e], [])
    Right core -> case compile core of
      Left e -> pure (["FAIL " ++ path ++ ": " ++ show e], [])
      Right mono -> do
        let got = reduce (evalProgram mono)
            fails = ["FAIL " ++ path ++ ": evaluator gave " ++ show got ++ ", expected " ++ show expected | got /= expected]
        pure (fails, [(path, core)])

main :: IO ()
main = do
  dir <- (</> "keel-native-tests") <$> getTemporaryDirectory
  createDirectoryIfMissing True dir
  loaded <- mapM loadExample exampleFiles
  modErrs <- (++) <$> (concat <$> mapM checkModuleError moduleErrors) <*> lspChecks
  let programs = cases ++ specCases ++ concatMap snd loaded
  failures <- (\fs -> concatMap fst loaded ++ modErrs ++ fs) . concat <$> forM (zip [0 :: Int ..] programs) (uncurry (runCase dir False))
  -- The examples have source positions: build them again with debug info.
  let debugPrograms = concatMap snd loaded
  debugFailures <- concat <$> forM (zip [0 :: Int ..] debugPrograms) (uncurry (runCase dir True))
  let refused =
        [ "FAIL " ++ name ++ ": expected 'not supported yet', got " ++ either id (const "assembly") r
        | (name, p) <- unsupportedCases
        , let r = compileNative p
        , either (not . ("not supported yet" `isInfixOf`)) (const True) r
        ]
      allFailures = failures ++ debugFailures ++ refused
      total = length programs + length debugPrograms + length unsupportedCases + length exampleFiles + length moduleErrors + 1
  mapM_ putStrLn allFailures
  putStrLn (show (total - length allFailures) ++ "/" ++ show total ++ " native cases passed")
  rvFailures <-
    findRiscVTools >>= \case
      Nothing -> putStrLn "RISC-V: llvm, lld or qemu not found; skipped" >> pure []
      Just tools -> do
        fs <- concat <$> forM (zip [0 :: Int ..] programs) (uncurry (runRiscV tools dir))
        fw <- firmware tools dir
        let n = length programs + 1
            bad = fs ++ fw
        mapM_ putStrLn bad
        putStrLn (show (n - length bad) ++ "/" ++ show n ++ " RISC-V cases passed (QEMU virt)")
        pure bad
  unless (null allFailures && null rvFailures) exitFailure

-- | Compile for RISC-V, boot in QEMU, and compare with the reference evaluator.
runRiscV :: RiscVTools -> FilePath -> Int -> (String, Program) -> IO [String]
runRiscV tools dir i (name, prog) = case (compile prog, compileRiscV prog) of
  (Left e, _) -> pure [failMsg ("does not type-check: " ++ show e)]
  (_, Left e) -> pure [failMsg e]
  (Right mono, Right asm) ->
    buildRiscV tools (dir </> ("rv" ++ show i)) asm >>= \case
      Left e -> pure [failMsg e]
      Right elf -> do
        (code, uart) <- runQemu tools elf
        -- The UART carries everything: the program's output, then a panic message or the
        -- result and statistics lines.
        let (body, stats) = case breakLast "keel-stats:" uart of
              Just (before, after) -> (before, parseStats ("keel-stats:" ++ after))
              Nothing -> (maybe uart fst (breakLast "panic: " uart), Nothing)
            native = parseRun code body
            reference = reduce (evalProgram mono)
        pure $
          [failMsg ("RISC-V " ++ show native ++ ", reference " ++ show reference) | native /= Just reference]
            ++ [failMsg ("leak: " ++ show stats) | code == ExitSuccess, fmap live stats /= Just 0]
  where
    failMsg msg = "FAIL [riscv] " ++ name ++ ": " ++ msg

-- | The firmware example drives the board's UART itself.
firmware :: RiscVTools -> FilePath -> IO [String]
firmware tools dir = do
  let path = "examples/firmware/hello.kl"
  loaded <- loadModules path
  case loaded >>= either (Left . show) Right . inferProgram . fst >>= compileRiscV of
    Left e -> pure ["FAIL [riscv] " ++ path ++ ": " ++ e]
    Right asm ->
      buildRiscV tools (dir </> "firmware") asm >>= \case
        Left e -> pure ["FAIL [riscv] " ++ path ++ ": " ++ e]
        Right elf -> do
          (code, uart) <- runQemu tools elf
          pure ["FAIL [riscv] " ++ path ++ ": got " ++ show (code, uart) | code /= ExitSuccess || not ("Hi!\nresult: ()\n" `isPrefixOf` uart)]

-- | Build and run a program natively, and compare with the evaluator. With @debug@, it is built
-- as keelc build -g does: positions kept through optimization and a line table, which must
-- change nothing but the debug info.
runCase :: FilePath -> Bool -> Int -> (String, Program) -> IO [String]
runCase dir debug i (name, prog) = case (compile prog, compileNativeWith debug prog) of
  (Left e, _) -> pure [failMsg ("does not type-check: " ++ show e)]
  (_, Left e) -> pure [failMsg e]
  (_, Right asm) | debug, not (".loc " `isInfixOf` asm) -> pure [failMsg "no line table"]
  (Right mono, Right asm) -> do
    let base = (if debug then "dcase" else "case") ++ show i
        src = dir </> (base ++ ".s")
        exe = dir </> base
    writeFile src asm
    (ccCode, _, ccErr) <- readProcessWithExitCode "cc" (["-g" | debug] ++ ["-o", exe, src]) ""
    case ccCode of
      ExitFailure _ -> pure [failMsg ("cc failed:\n" ++ ccErr)]
      ExitSuccess -> do
        environment <- getEnvironment
        (code, stdout, stderr) <- readCreateProcessWithExitCode ((proc exe []) {env = Just (("KEEL_STATS", "1") : environment)}) ""
        let native = parseRun code stdout
            reference = reduce (evalProgram mono)
            stats = parseStats stderr
        pure $
          [failMsg ("native " ++ show native ++ ", reference " ++ show reference) | native /= Just reference]
            ++ [failMsg ("leak: " ++ show stats) | code == ExitSuccess, fmap live stats /= Just 0]
            ++ [ failMsg ("expected most cells to be reused in place: " ++ show stats)
               | name == "examples/reuse.kl"
               , maybe True (\s -> inplace s < 990000 || allocs s > 5000) stats
               ]
  where
    failMsg msg = "FAIL " ++ name ++ (if debug then " (-g)" else "") ++ ": " ++ msg

data Stats = Stats {allocs, recycled, inplace, freed, live :: Integer}
  deriving (Show)

-- | Parse @keel-stats: allocs=… recycled=… inplace=… freed=… live=…@ from stderr.
parseStats :: String -> Maybe Stats
parseStats err = case [l | l <- lines err, "keel-stats:" `isInfixOf` l] of
  l : _ -> case mapM (readNum . drop 1 . dropWhile (/= '=')) (drop 1 (words l)) of
    Just [a, r, i, f, v] -> Just (Stats a r i f v)
    _ -> Nothing
  [] -> Nothing
  where
    readNum s = case reads s of
      [(n, "")] -> Just n
      _ -> Nothing

-- | (result line or Nothing for a panic, output text)
type Run = (Maybe String, String)

reduce :: (Outcome, String) -> Run
reduce (Done v, out') = (Just (show v), out')
reduce (Panicked _, out') = (Nothing, out')

-- | Split at the last occurrence of a marker: (before, after it).
breakLast :: String -> String -> Maybe (String, String)
breakLast needle hay = case [i | i <- [0 .. length hay - length needle], needle `isPrefixOf` drop i hay] of
  [] -> Nothing
  is -> let i = last is in Just (take i hay, drop (i + length needle) hay)

-- | A finished run prints its output, then @result: …@ and a newline; a panic (exit 101)
-- leaves just the output.
parseRun :: ExitCode -> String -> Maybe Run
parseRun code text = case code of
  ExitSuccess
    | Just (before, after) <- breakLast "result: " text
    , Just r <- stripSuffix' "\n" after ->
        Just (Just r, before)
  ExitFailure 101 -> Just (Nothing, text)
  _ -> Nothing
  where
    stripSuffix' suf s = reverse <$> stripPrefix (reverse suf) (reverse s)
