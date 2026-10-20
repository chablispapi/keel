-- | Stage 1 examples from spec/core.md §1.6: each program either evaluates to an expected
-- value or is rejected with an expected error class.
module Main (main) where

import Control.Monad (unless)
import Keel.Check
import Keel.Eval
import Keel.Syntax
import System.Exit (exitFailure)

data Expect = Gives Value | Rejects ErrKind

-- Shared declarations ------------------------------------------------------------------

intList, token :: Decl
intList = Data False "IntList" [("Nil", []), ("Cons", [TInt, TBox (TData "IntList")])]
token = Data True "Token" [("Token", [])]

tList, tTok :: Ty
tList = TData "IntList"
tTok = TData "Token"

-- def consume : Token → Int = λ(t:Token). case t of { Token → 1 }
consume :: Decl
consume = Def "consume" (TFun tTok TInt) (Lam "t" tTok (Case (Var "t") [("Token", [], IntLit 1)]))

-- def map : (Int → Int) → IntList → IntList
mapDef :: Decl
mapDef =
  Def "map" (TFun (TFun TInt TInt) (TFun tList tList)) $
    Lam "f" (TFun TInt TInt) $
      Lam "xs" tList $
        Case
          (Var "xs")
          [ ("Nil", [], Con "Nil" [])
          , ( "Cons"
            , ["x", "rest"]
            , Con "Cons" [App (Var "f") (Var "x"), Box (App (App (Var "map") (Var "f")) (Unbox (Var "rest")))]
            )
          ]

-- def sum : IntList → Int
sumDef :: Decl
sumDef =
  Def "sum" (TFun tList TInt) $
    Lam "ys" tList $
      Case
        (Var "ys")
        [ ("Nil", [], IntLit 0)
        , ("Cons", ["y", "more"], Prim Add (Var "y") (App (Var "sum") (Unbox (Var "more"))))
        ]

incDef :: Decl
incDef = Def "inc" (TFun TInt TInt) (Lam "n" TInt (Prim Add (Var "n") (IntLit 1)))

list :: [Integer] -> Term
list = foldr (\n t -> Con "Cons" [IntLit n, Box t]) (Con "Nil" [])

withToken :: Term -> Program
withToken = Program [token, consume]

letTok :: Term -> Term
letTok = Let "t" (Con "Token" [])

-- Cases ---------------------------------------------------------------------------------

cases :: [(String, Program, Expect)]
cases =
  [ ( "let/if/arith"
    , Program [] (Let "x" (IntLit 2) (If (Prim Lt (Var "x") (IntLit 3)) (Prim Mul (Var "x") (IntLit 10)) (IntLit 0)))
    , Gives (VInt 20)
    )
  , ( "recursive map + sum"
    , Program [intList, mapDef, sumDef, incDef] (App (Var "sum") (App (App (Var "map") (Var "inc")) (list [1, 2, 3])))
    , Gives (VInt 9)
    )
  , ( "map returns data"
    , Program [intList, mapDef, incDef] (App (App (Var "map") (Var "inc")) (list [1, 2]))
    , Gives (VCon "Cons" [VInt 2, VBox (VCon "Cons" [VInt 3, VBox (VCon "Nil" [])])])
    )
  , ("linear argument to free function", withToken (letTok (App (Var "consume") (Var "t"))), Gives (VInt 1))
  , ( "linear closure called once"
    , withToken (letTok (Let "k" (LLam "n" TInt (Prim Add (App (Var "consume") (Var "t")) (Var "n"))) (App (Var "k") (IntLit 41))))
    , Gives (VInt 42)
    )
  , ( "linear data with linear field"
    , Program
        [token, consume, Data True "Pair" [("P", [tTok, TInt])]]
        ( Case
            (Con "P" [Con "Token" [], IntLit 5])
            [("P", ["t", "n"], Prim Add (App (Var "consume") (Var "t")) (Var "n"))]
        )
    , Gives (VInt 6)
    )
  , ( "linear var used in both branches"
    , withToken (letTok (If (BoolLit True) (App (Var "consume") (Var "t")) (Prim Add (App (Var "consume") (Var "t")) (IntLit 1))))
    , Gives (VInt 1)
    )
  , -- rejected
    ( "duplicate use"
    , withToken (letTok (Prim Add (App (Var "consume") (Var "t")) (App (Var "consume") (Var "t"))))
    , Rejects Duplicate
    )
  , ("dropped linear value", withToken (letTok (IntLit 1)), Rejects Dropped)
  , ( "used in one branch only"
    , withToken (letTok (If (BoolLit True) (App (Var "consume") (Var "t")) (IntLit 0)))
    , Rejects BranchMismatch
    )
  , ( "free closure captures linear"
    , withToken (letTok (Let "k" (Lam "n" TInt (App (Var "consume") (Var "t"))) (App (Var "k") (IntLit 1))))
    , Rejects LinearCapture
    )
  , ( "linear closure called twice"
    , withToken
        ( letTok
            ( Let
                "k"
                (LLam "n" TInt (App (Var "consume") (Var "t")))
                (Prim Add (App (Var "k") (IntLit 1)) (App (Var "k") (IntLit 2)))
            )
        )
    , Rejects Duplicate
    )
  , ("free data with linear field", Program [token, Data False "Bad" [("B", [tTok])]] (IntLit 0), Rejects LinearField)
  , ("unboxed recursion", Program [Data False "L" [("N", []), ("C", [TInt, TData "L"])]] (IntLit 0), Rejects InfiniteSize)
  , ( "mutual unboxed recursion"
    , Program [Data False "A" [("MkA", [TData "B"])], Data False "B" [("MkB", [TData "A"]), ("E", [])]] (IntLit 0)
    , Rejects InfiniteSize
    )
  , ("non-exhaustive case", Program [intList] (Case (Con "Nil" []) [("Nil", [], IntLit 0)]), Rejects NonExhaustive)
  , ("type mismatch", Program [] (Prim Add (IntLit 1) (BoolLit True)), Rejects Mismatch)
  , ("shadowing", Program [] (Let "x" (IntLit 1) (Let "x" (IntLit 2) (Var "x"))), Rejects Shadowing)
  ]

-- Runner --------------------------------------------------------------------------------

main :: IO ()
main = do
  failures <- concat <$> mapM run cases
  mapM_ putStrLn failures
  putStrLn (show (length cases - length failures) ++ "/" ++ show (length cases) ++ " passed")
  unless (null failures) exitFailure
  where
    run (name, prog, expect) = pure $ case (checkProgram prog, expect) of
      (Right _, Gives v) ->
        let got = evalProgram prog in [failMsg name ("expected " ++ show v ++ ", got " ++ show got) | got /= v]
      (Left (TypeError k _), Rejects k') -> [failMsg name ("expected " ++ show k' ++ ", got " ++ show k) | k /= k']
      (Left e, Gives _) -> [failMsg name ("unexpected rejection: " ++ show e)]
      (Right t, Rejects k) -> [failMsg name ("expected " ++ show k ++ ", but accepted at type " ++ show t)]
    failMsg name msg = "FAIL " ++ name ++ ": " ++ msg
