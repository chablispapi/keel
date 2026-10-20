-- | Examples from spec/core.md §1.6 and §2.7: each program either evaluates to an expected
-- value (and output trace), panics, or is rejected with an expected error class.
module Main (main) where

import Control.Monad (unless)
import Data.Set qualified as S
import Keel.Check
import Keel.Eval
import Keel.Syntax
import System.Exit (exitFailure)

data Expect
  = Gives Value [Integer] -- ^ result and @out@ trace
  | Panics [Integer]      -- ^ panics after writing this trace
  | Rejects ErrKind

ok :: Value -> Expect
ok v = Gives v []

-- Helpers -------------------------------------------------------------------------------

tI :: Ty
tI = TInt i64

int :: Integer -> Term
int = IntLit i64

fn :: Ty -> Ty -> Ty
fn a = TFun a S.empty

fnE :: [String] -> Ty -> Ty -> Ty
fnE es a = TFun a (S.fromList es)

add, mul, eq :: Term -> Term -> Term
add = Prim (Arith Checked Add)
mul = Prim (Arith Checked Mul)
eq = Prim Eq

-- Shared declarations ---------------------------------------------------------------------

intList, token :: Decl
intList = Data False "IntList" [("Nil", []), ("Cons", [tI, TBox (TData "IntList")])]
token = Data True "Token" [("Token", [])]

tList, tTok :: Ty
tList = TData "IntList"
tTok = TData "Token"

-- def consume : Token → i64 = λ(t:Token). case t of { Token → 1 }
consume :: Decl
consume = Def "consume" (fn tTok tI) (Lam "t" tTok (Case (Var "t") [("Token", [], int 1)]))

-- def map : (i64 →{Panic} i64) → IntList →{Panic, Diverge} IntList
mapDef :: Decl
mapDef =
  Def "map" (fn (fnE [panicE] tI tI) (fnE [panicE, divergeE] tList tList)) $
    Lam "f" (fnE [panicE] tI tI) $
      Lam "xs" tList $
        Case
          (Var "xs")
          [ ("Nil", [], Con "Nil" [])
          , ( "Cons"
            , ["x", "rest"]
            , Con "Cons" [App (Var "f") (Var "x"), Box (App (App (Var "map") (Var "f")) (Unbox (Var "rest")))]
            )
          ]

-- def sum : IntList →{Panic, Diverge} i64
sumDef :: Decl
sumDef =
  Def "sum" (fnE [panicE, divergeE] tList tI) $
    Lam "ys" tList $
      Case
        (Var "ys")
        [ ("Nil", [], int 0)
        , ("Cons", ["y", "more"], add (Var "y") (App (Var "sum") (Unbox (Var "more"))))
        ]

incDef :: Decl
incDef = Def "inc" (fnE [panicE] tI tI) (Lam "n" tI (add (Var "n") (int 1)))

list :: [Integer] -> Term
list = foldr (\n t -> Con "Cons" [int n, Box t]) (Con "Nil" [])

withToken :: Term -> Program
withToken = Program [token, consume]

letTok :: Term -> Term
letTok = Let "t" (Con "Token" [])

-- effect MMIO { read : i64 ⇒ i64 ; write : W ⇒ Unit },  data W = W(i64, i64)
mmio, wData :: Decl
mmio = Effect "MMIO" [("read", tI, tI), ("write", TData "W", TUnit)]
wData = Data False "W" [("W", [tI, tI])]

-- def send : IntList →{MMIO, Diverge} Unit
--   = λxs. case xs of
--       Nil → ()
--       Cons(c, rest) → if read(4) == 1 then let done = write(W(0, c)) in send (unbox rest)
--                       else send (Cons(c, rest))
sendDef :: Decl
sendDef =
  Def "send" (fnE ["MMIO", divergeE] tList TUnit) $
    Lam "xs" tList $
      Case
        (Var "xs")
        [ ("Nil", [], UnitLit)
        , ( "Cons"
          , ["c", "rest"]
          , If
              (eq (Perform "read" (int 4)) (int 1))
              (Let "done" (Perform "write" (Con "W" [int 0, Var "c"])) (App (Var "send") (Unbox (Var "rest"))))
              (App (Var "send") (Con "Cons" [Var "c", Var "rest"]))
          )
        ]

-- A mock UART: the status register always reads 1 (ready), writes go to the output trace.
mockUart :: Term -> Term
mockUart body =
  Handle
    "MMIO"
    body
    [ ("read", "addr", int 1)
    , ("write", "w", Case (Var "w") [("W", ["reg", "v"], Perform "out" (Var "v"))])
    ]

-- Cases -----------------------------------------------------------------------------------

cases :: [(String, Program, Expect)]
cases =
  -- Stage 1 -------------------------------------------------------------------------------
  [ ( "let/if/arith"
    , Program [] (Let "x" (int 2) (If (Prim Lt (Var "x") (int 3)) (mul (Var "x") (int 10)) (int 0)))
    , ok (VInt i64 20)
    )
  , ( "recursive map + sum"
    , Program [intList, mapDef, sumDef, incDef] (App (Var "sum") (App (App (Var "map") (Var "inc")) (list [1, 2, 3])))
    , ok (VInt i64 9)
    )
  , ( "map returns data"
    , Program [intList, mapDef, incDef] (App (App (Var "map") (Var "inc")) (list [1, 2]))
    , ok (VCon "Cons" [VInt i64 2, VBox (VCon "Cons" [VInt i64 3, VBox (VCon "Nil" [])])])
    )
  , ("linear argument to free function", withToken (letTok (App (Var "consume") (Var "t"))), ok (VInt i64 1))
  , ( "linear closure called once"
    , withToken (letTok (Let "k" (LLam "n" tI (add (App (Var "consume") (Var "t")) (Var "n"))) (App (Var "k") (int 41))))
    , ok (VInt i64 42)
    )
  , ( "linear data with linear field"
    , Program
        [token, consume, Data True "Pair" [("P", [tTok, tI])]]
        (Case (Con "P" [Con "Token" [], int 5]) [("P", ["t", "n"], add (App (Var "consume") (Var "t")) (Var "n"))])
    , ok (VInt i64 6)
    )
  , ( "linear var used in both branches"
    , withToken (letTok (If (BoolLit True) (App (Var "consume") (Var "t")) (add (App (Var "consume") (Var "t")) (int 1))))
    , ok (VInt i64 1)
    )
  , ( "duplicate use"
    , withToken (letTok (add (App (Var "consume") (Var "t")) (App (Var "consume") (Var "t"))))
    , Rejects Duplicate
    )
  , ("dropped linear value", withToken (letTok (int 1)), Rejects Dropped)
  , ( "used in one branch only"
    , withToken (letTok (If (BoolLit True) (App (Var "consume") (Var "t")) (int 0)))
    , Rejects BranchMismatch
    )
  , ( "free closure captures linear"
    , withToken (letTok (Let "k" (Lam "n" tI (App (Var "consume") (Var "t"))) (App (Var "k") (int 1))))
    , Rejects LinearCapture
    )
  , ( "linear closure called twice"
    , withToken (letTok (Let "k" (LLam "n" tI (App (Var "consume") (Var "t"))) (add (App (Var "k") (int 1)) (App (Var "k") (int 2)))))
    , Rejects Duplicate
    )
  , ("free data with linear field", Program [token, Data False "Bad" [("B", [tTok])]] (int 0), Rejects LinearField)
  , ("unboxed recursion", Program [Data False "L" [("N", []), ("C", [tI, TData "L"])]] (int 0), Rejects InfiniteSize)
  , ( "mutual unboxed recursion"
    , Program [Data False "A" [("MkA", [TData "B"])], Data False "B" [("MkB", [TData "A"]), ("E", [])]] (int 0)
    , Rejects InfiniteSize
    )
  , ("non-exhaustive case", Program [intList] (Case (Con "Nil" []) [("Nil", [], int 0)]), Rejects NonExhaustive)
  , ("type mismatch", Program [] (add (int 1) (BoolLit True)), Rejects Mismatch)
  , ("shadowing", Program [] (Let "x" (int 1) (Let "x" (int 2) (Var "x"))), Rejects Shadowing)
  -- Stage 2 -------------------------------------------------------------------------------
  , ( "mock UART handler"
    , Program [intList, wData, mmio, sendDef] (mockUart (App (Var "send") (list [72, 105])))
    , Gives VUnit [72, 105]
    )
  , ( "handler clause reaches the outer handler"
    , Program [] (Handle ioE (Perform "out" (int 5)) [("out", "x", Perform "out" (mul (Var "x") (int 10)))])
    , Gives VUnit [50]
    )
  , ("wrapping add", Program [] (Prim (Arith Wrap Add) (IntLit u8 250) (IntLit u8 10)), ok (VInt u8 4))
  , ("wrapping mul, signed", Program [] (Prim (Arith Wrap Mul) (IntLit i8 100) (IntLit i8 2)), ok (VInt i8 (-56)))
  , ("saturating add", Program [] (Prim (Arith Saturate Add) (IntLit u8 250) (IntLit u8 10)), ok (VInt u8 255))
  , ("saturating sub, signed", Program [] (Prim (Arith Saturate Sub) (IntLit i8 (-100)) (IntLit i8 100)), ok (VInt i8 (-128)))
  , ("checked overflow panics", Program [] (add (IntLit u8 250) (IntLit u8 10)), Panics [])
  , ( "output before a panic is kept"
    , Program [] (Let "a" (Perform "out" (int 1)) (add (IntLit u8 250) (IntLit u8 10)))
    , Panics [1]
    )
  , ( "pure function where Panic is allowed"
    , Program
        [intList, mapDef, sumDef, Def "double" (fn tI tI) (Lam "n" tI (Prim (Arith Wrap Mul) (Var "n") (int 2)))]
        (App (Var "sum") (App (App (Var "map") (Var "double")) (list [1, 2, 3])))
    , ok (VInt i64 12)
    )
  , ( "free function where a linear one is expected"
    , Program
        [Def "apply1" (fn (TLFun tI S.empty tI) tI) (Lam "g" (TLFun tI S.empty tI) (App (Var "g") (int 1)))]
        (App (Var "apply1") (Lam "n" tI (Prim (Arith Wrap Add) (Var "n") (int 1))))
    , ok (VInt i64 2)
    )
  , ("unhandled effect", Program [mmio, wData] (Perform "read" (int 4)), Rejects Unhandled)
  , ( "effect missing from signature"
    , Program [Def "bad" (fn tI tI) (Lam "n" tI (add (Var "n") (int 1)))] (int 0)
    , Rejects EffectMismatch
    )
  , ( "recursion without Diverge"
    , Program [Def "loop" (fn tI tI) (Lam "n" tI (App (Var "loop") (Var "n")))] (int 0)
    , Rejects EffectMismatch
    )
  , ( "recursion hidden in an argument"
    , Program
        [ Def "twice" (fn (fn tI tI) (fn tI tI)) (Lam "g" (fn tI tI) (Lam "m" tI (App (Var "g") (Var "m"))))
        , Def "f" (fn tI tI) (Lam "k" tI (App (App (Var "twice") (Var "f")) (Var "k")))
        ]
        (int 0)
    , Rejects EffectMismatch
    )
  , ("non-positive data", Program [Data False "T" [("MkT", [fn (TData "T") tI])]] (int 0), Rejects NonPositive)
  , ( "handler clause captures linear"
    , withToken (letTok (Handle ioE (Perform "out" (int 1)) [("out", "x", Let "r" (App (Var "consume") (Var "t")) UnitLit)]))
    , Rejects LinearCapture
    )
  , ( "handler misses an operation"
    , Program [mmio, wData] (Handle "MMIO" (Perform "read" (int 4)) [("read", "addr", int 1)])
    , Rejects NonExhaustive
    )
  , ("Panic cannot be handled", Program [] (Handle panicE (int 1) []), Rejects Unbound)
  , ("mixed integer widths", Program [] (add (IntLit u8 1) (int 1)), Rejects Mismatch)
  , ("literal out of range", Program [] (IntLit u8 300), Rejects Mismatch)
  ]

-- Runner --------------------------------------------------------------------------------

main :: IO ()
main = do
  let failures = concatMap run cases
  mapM_ putStrLn failures
  putStrLn (show (length cases - length failures) ++ "/" ++ show (length cases) ++ " passed")
  unless (null failures) exitFailure
  where
    run (name, prog, expect) = case (checkProgram prog, expect) of
      (Left (TypeError k _), Rejects k') -> [failMsg name ("expected " ++ show k' ++ ", got " ++ show k) | k /= k']
      (Left e, _) -> [failMsg name ("unexpected rejection: " ++ show e)]
      (Right t, Rejects k) -> [failMsg name ("expected " ++ show k ++ ", but accepted at " ++ show t)]
      (Right _, _) -> case (evalProgram prog, expect) of
        ((Done v, tr), Gives v' tr') | v == v' && tr == tr' -> []
        ((Panicked _, tr), Panics tr') | tr == tr' -> []
        (got, _) -> [failMsg name ("got " ++ show got)]
    failMsg name msg = "FAIL " ++ name ++ ": " ++ msg
