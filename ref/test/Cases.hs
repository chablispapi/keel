-- | Examples from spec/core.md §1.6, §2.7, §3.6 and §4.6: each program either evaluates to an expected
-- value (and output trace), panics, or is rejected with an expected error class.
module Cases (Expect (..), cases) where

import Data.Set qualified as S
import Keel.Check
import Keel.Eval
import Keel.Syntax

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
intList = Data False "IntList" [] [("Nil", []), ("Cons", [tI, TBox (TData "IntList" [])])]
token = Data True "Token" [] [("Token", [])]

tList, tTok :: Ty
tList = TData "IntList" []
tTok = TData "Token" []

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
          [ ("Nil", [], Con "Nil" [] [])
          , ( "Cons"
            , ["x", "rest"]
            , Con "Cons" [] [App (Var "f") (Var "x"), Box (App (App (Var "map") (Var "f")) (Unbox (Var "rest")))]
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
list = foldr (\n t -> Con "Cons" [] [int n, Box t]) (Con "Nil" [] [])

withToken :: Term -> Program
withToken = Program [token, consume]

letTok :: Term -> Term
letTok = Let "t" (Con "Token" [] [])

-- effect MMIO { read : i64 ⇒ i64 ; write : W ⇒ Unit },  data W = W(i64, i64)
mmio, wData :: Decl
mmio = Effect "Port" [("read", tI, tI), ("write", TData "W" [], TUnit)]
wData = Data False "W" [] [("W", [tI, tI])]

-- def send : IntList →{MMIO, Diverge} Unit
--   = λxs. case xs of
--       Nil → ()
--       Cons(c, rest) → if read(4) == 1 then let done = write(W(0, c)) in send (unbox rest)
--                       else send (Cons(c, rest))
sendDef :: Decl
sendDef =
  Def "send" (fnE ["Port", divergeE] tList TUnit) $
    Lam "xs" tList $
      Case
        (Var "xs")
        [ ("Nil", [], UnitLit)
        , ( "Cons"
          , ["c", "rest"]
          , If
              (eq (Perform "read" (int 4)) (int 1))
              (Let "done" (Perform "write" (Con "W" [] [int 0, Var "c"])) (App (Var "send") (Unbox (Var "rest"))))
              (App (Var "send") (Con "Cons" [] [Var "c", Var "rest"]))
          )
        ]

-- A mock UART: the status register always reads 1 (ready), writes go to the output trace.
mockUart :: Term -> Term
mockUart body =
  Handle
    "Port"
    body
    [ ("read", "addr", int 1)
    , ("write", "w", Case (Var "w") [("W", ["reg", "v"], Perform "out" (Var "v"))])
    ]

-- Stage 3 declarations -------------------------------------------------------------------

-- def bump : &mut i64 →{Panic} Unit = λ(&mut n:i64). n := n + 1
bumpDef :: Decl
bumpDef = Def "bump" (fnE [panicE] (TMut tI) TUnit) (Lam "n" (TMut tI) (Assign "n" (add (Var "n") (int 1))))

-- linear data Counter = Counter(i64)
-- def tick : &mut Counter → Unit = λ(&mut c:Counter). case c of Counter(n) → c := Counter(n +% 1)
counter, tickDef :: Decl
counter = Data True "Counter" [] [("Counter", [tI])]
tickDef =
  Def "tick" (fn (TMut (TData "Counter" [])) TUnit) $
    Lam "c" (TMut (TData "Counter" [])) $
      Case (Var "c") [("Counter", ["n"], Assign "c" (Con "Counter" [] [Prim (Arith Wrap Add) (Var "n") (int 1)]))]

-- def drain : &mut IntList →{MMIO, Diverge} Unit = λ(&mut q:IntList). case q of
--   Nil → ()
--   Cons(c, rest) → write(W(0, c)); q := unbox rest; drain(&mut q)
drainDef :: Decl
drainDef =
  Def "drain" (fnE ["Port", divergeE] (TMut tList) TUnit) $
    Lam "q" (TMut tList) $
      Case
        (Var "q")
        [ ("Nil", [], UnitLit)
        , ( "Cons"
          , ["c", "rest"]
          , Seq
              (Perform "write" (Con "W" [] [int 0, Var "c"]))
              (Seq (Assign "q" (Unbox (Var "rest"))) (App (Var "drain") (BorrowMut "q")))
          )
        ]

-- The same function written by hand in state-passing style:
-- def drainSP : IntList →{MMIO, Diverge} Unit ⊗ IntList = λ(q:IntList). case q of
--   Nil → ((), q)
--   Cons(c, rest) → let d = write(W(0, c)) in drainSP (unbox rest)
drainSPDef :: Decl
drainSPDef =
  Def "drainSP" (fnE ["Port", divergeE] tList (TPair TUnit tList)) $
    Lam "q" tList $
      Case
        (Var "q")
        [ ("Nil", [], Pair UnitLit (Var "q"))
        , ( "Cons"
          , ["c", "rest"]
          , Let "d" (Perform "write" (Con "W" [] [int 0, Var "c"])) (App (Var "drainSP") (Unbox (Var "rest")))
          )
        ]

-- def len : &IntList →{Diverge} i64 = λ(&xs:IntList). case xs of
--   Nil → 0
--   Cons(y, more) → var m = unbox more in len(&m) +% 1
lenDef :: Decl
lenDef =
  Def "len" (fnE [divergeE] (TRef tList) tI) $
    Lam "xs" (TRef tList) $
      Case
        (Var "xs")
        [ ("Nil", [], int 0)
        , ("Cons", ["y", "more"], LetVar "m" (Unbox (Var "more")) (Prim (Arith Wrap Add) (App (Var "len") (Borrow "m")) (int 1)))
        ]

-- Stage 4 declarations -------------------------------------------------------------------

tA, tB :: Ty
tA = TVar "a"
tB = TVar "b"

tL :: Ty -> Ty
tL a = TData "List" [a]

-- data List a = Nil | Cons(a, Box (List a))
listD :: Decl
listD = Data False "List" ["a"] [("Nil", []), ("Cons", [tA, TBox (tL tA)])]

plist :: Ty -> [Term] -> Term
plist t = foldr (\x r -> Con "Cons" [t] [x, Box r]) (Con "Nil" [t] [])

vlist :: [Integer] -> Value
vlist = foldr (\n r -> VCon "Cons" [VInt i64 n, VBox r]) (VCon "Nil" [])

-- def pmap : ∀a b 'e. (a →'e b) → List a →{'e, Diverge} List b
pmapDef :: Decl
pmapDef =
  Def "pmap" (TForall [("a", Lin), ("b", Lin)] ["'e"] (fn (fnE ["'e"] tA tB) (fnE ["'e", divergeE] (tL tA) (tL tB)))) $
    Lam "f" (fnE ["'e"] tA tB) $
      Lam "xs" (tL tA) $
        Case
          (Var "xs")
          [ ("Nil", [], Con "Nil" [tB] [])
          , ( "Cons"
            , ["x", "rest"]
            , Con "Cons" [tB] [App (Var "f") (Var "x"), Box (App (App (TyApp "pmap" [tA, tB] [S.singleton "'e"]) (Var "f")) (Unbox (Var "rest")))]
            )
          ]

-- def psum : List i64 →{Panic, Diverge} i64
psumDef :: Decl
psumDef =
  Def "psum" (fnE [panicE, divergeE] (tL tI) tI) $
    Lam "ys" (tL tI) $
      Case (Var "ys") [("Nil", [], int 0), ("Cons", ["y", "more"], add (Var "y") (App (Var "psum") (Unbox (Var "more"))))]

-- codata Serial { send : i64 →{IO} Unit }, two implementations, and a client.
serialD, loudDef, quietDef, greetDef :: Decl
serialD = Codata "Serial" [] [("send", fnE [ioE] tI TUnit)]
loudDef = Def "loud" (TData "Serial" []) (Cocase "Serial" [] [("send", Lam "c" tI (Perform "out" (Var "c")))])
quietDef = Def "quiet" (TData "Serial" []) (Cocase "Serial" [] [("send", Lam "c" tI UnitLit)])
greetDef =
  Def "greet" (fnE [ioE] (TData "Serial" []) TUnit) $
    Lam "s" (TData "Serial" []) (Seq (App (Proj (Var "s") "send") (int 72)) (App (Proj (Var "s") "send") (int 105)))

-- codata Ord a { lt : a → a → Bool }: an explicit dictionary.
ordD :: Decl
ordD = Codata "Ord" ["a"] [("lt", fn tA (fn tA TBool))]

tOrd :: Ty -> Ty
tOrd a = TData "Ord" [a]

-- def insert : ∀(a:Free). Ord a → a → List a →{Diverge} List a
insertDef :: Decl
insertDef =
  Def "insert" (TForall [("a", Free)] [] (fn (tOrd tA) (fn tA (fnE [divergeE] (tL tA) (tL tA))))) $
    Lam "o" (tOrd tA) $
      Lam "x" tA $
        Lam "xs" (tL tA) $
          Case
            (Var "xs")
            [ ("Nil", [], Con "Cons" [tA] [Var "x", Box (Con "Nil" [tA] [])])
            , ( "Cons"
              , ["y", "rest"]
              , If
                  (App (App (Proj (Var "o") "lt") (Var "x")) (Var "y"))
                  (Con "Cons" [tA] [Var "x", Box (Con "Cons" [tA] [Var "y", Var "rest"])])
                  (Con "Cons" [tA] [Var "y", Box (App (App (App (TyApp "insert" [tA] []) (Var "o")) (Var "x")) (Unbox (Var "rest")))])
              )
            ]

-- def sort : ∀(a:Free). Ord a → List a →{Diverge} List a
sortDef :: Decl
sortDef =
  Def "sort" (TForall [("a", Free)] [] (fn (tOrd tA) (fnE [divergeE] (tL tA) (tL tA)))) $
    Lam "o2" (tOrd tA) $
      Lam "zs" (tL tA) $
        Case
          (Var "zs")
          [ ("Nil", [], Con "Nil" [tA] [])
          , ( "Cons"
            , ["z", "more"]
            , App (App (App (TyApp "insert" [tA] []) (Var "o2")) (Var "z")) (App (App (TyApp "sort" [tA] []) (Var "o2")) (Unbox (Var "more")))
            )
          ]

ordI64, ordDesc :: Decl
ordI64 = Def "ordI64" (tOrd tI) (Cocase "Ord" [tI] [("lt", Lam "p" tI (Lam "q" tI (Prim Lt (Var "p") (Var "q"))))])
ordDesc = Def "ordDesc" (tOrd tI) (Cocase "Ord" [tI] [("lt", Lam "p" tI (Lam "q" tI (Prim Lt (Var "q") (Var "p"))))])

sortWith :: String -> Term
sortWith o = App (App (TyApp "sort" [tI] []) (Var o)) (plist tI (map int [3, 1, 2]))

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
        [token, consume, Data True "Pair" [] [("P", [tTok, tI])]]
        (Case (Con "P" [] [Con "Token" [] [], int 5]) [("P", ["t", "n"], add (App (Var "consume") (Var "t")) (Var "n"))])
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
  , ("free data with linear field", Program [token, Data False "Bad" [] [("B", [tTok])]] (int 0), Rejects LinearField)
  , ("unboxed recursion", Program [Data False "L" [] [("N", []), ("C", [tI, TData "L" []])]] (int 0), Rejects InfiniteSize)
  , ( "mutual unboxed recursion"
    , Program [Data False "A" [] [("MkA", [TData "B" []])], Data False "B" [] [("MkB", [TData "A" []]), ("E", [])]] (int 0)
    , Rejects InfiniteSize
    )
  , ("non-exhaustive case", Program [intList] (Case (Con "Nil" [] []) [("Nil", [], int 0)]), Rejects NonExhaustive)
  , ("type mismatch", Program [] (add (int 1) (BoolLit True)), Rejects Mismatch)
  , ("shadowing", Program [] (Let "x" (int 1) (Let "x" (int 2) (Var "x"))), Rejects Shadowing)
  -- Stage 2 -------------------------------------------------------------------------------
  , ( "mock UART handler"
    , Program [intList, wData, mmio, sendDef] (mockUart (App (Var "send") (list [72, 105])))
    , Gives VUnit [72, 105]
    )
  , ( "handler clause reaches the outer handler"
    , Program [] (Handle ioE (Perform "out" (int 5)) [("out", "x", Perform "out" (mul (Var "x") (int 10))), ("putc", "ch", Perform "putc" (Var "ch"))])
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
  , ("non-positive data", Program [Data False "T" [] [("MkT", [fn (TData "T" []) tI])]] (int 0), Rejects NonPositive)
  , ( "handler clause captures linear"
    , withToken (letTok (Handle ioE (Perform "out" (int 1)) [("out", "x", Let "r" (App (Var "consume") (Var "t")) UnitLit), ("putc", "ch", Perform "putc" (Var "ch"))]))
    , Rejects LinearCapture
    )
  , ( "handler misses an operation"
    , Program [mmio, wData] (Handle "Port" (Perform "read" (int 4)) [("read", "addr", int 1)])
    , Rejects NonExhaustive
    )
  , ("Panic cannot be handled", Program [] (Handle panicE (int 1) []), Rejects Unbound)
  , ("mixed integer widths", Program [] (add (IntLit u8 1) (int 1)), Rejects Mismatch)
  , ("literal out of range", Program [] (IntLit u8 300), Rejects Mismatch)
  -- Stage 3 -------------------------------------------------------------------------------
  , ( "&mut counter"
    , Program
        [bumpDef]
        (LetVar "c" (int 0) (Seq (App (Var "bump") (BorrowMut "c")) (Seq (App (Var "bump") (BorrowMut "c")) (mul (Var "c") (int 10)))))
    , ok (VInt i64 20)
    )
  , ( "&mut on a linear value"
    , Program
        [counter, tickDef]
        ( LetVar "k" (Con "Counter" [] [int 0]) $
            Seq (App (Var "tick") (BorrowMut "k")) $
              Seq (App (Var "tick") (BorrowMut "k")) $
                Case (Var "k") [("Counter", ["v"], Var "v")]
        )
    , ok (VInt i64 2)
    )
  , ( "drain with &mut"
    , Program [intList, wData, mmio, drainDef] (mockUart (LetVar "buf" (list [72, 105]) (Seq (App (Var "drain") (BorrowMut "buf")) (Var "buf"))))
    , Gives (VCon "Nil" []) [72, 105]
    )
  , ( "drain by hand, state passing"
    , Program [intList, wData, mmio, drainSPDef] (mockUart (LetPair "u" "buf" (App (Var "drainSP") (list [72, 105])) (Var "buf")))
    , Gives (VCon "Nil" []) [72, 105]
    )
  , ( "& borrow"
    , Program [intList, lenDef] (LetVar "l" (list [5, 6, 7]) (App (Var "len") (Borrow "l")))
    , ok (VInt i64 3)
    )
  , ("var holding a linear value", withToken (LetVar "t" (Con "Token" [] []) (App (Var "consume") (Var "t"))), ok (VInt i64 1))
  , ("returning a reference", Program [Def "f" (fn tI (TMut tI)) (Lam "x" tI (Var "x"))] (int 0), Rejects RefEscape)
  , ("reference in a data field", Program [Data False "D" [] [("D", [TRef tI])]] (int 0), Rejects RefEscape)
  , ( "borrow outside an argument"
    , Program [] (LetVar "x" (int 1) (Let "y" (BorrowMut "x") (int 0)))
    , Rejects RefEscape
    )
  , ( "closure captures a place"
    , Program [] (LetVar "x" (int 1) (Let "g" (Lam "u" TUnit (Var "x")) (App (Var "g") UnitLit)))
    , Rejects PlaceCapture
    )
  , ( "assign to a & parameter"
    , Program [Def "f" (fn (TRef tI) TUnit) (Lam "x" (TRef tI) (Assign "x" (int 1)))] (int 0)
    , Rejects NotMutable
    )
  , ("assign to a non-place", Program [] (Let "y" (int 1) (Assign "y" (int 2))), Rejects NotAPlace)
  , ("&mut of a non-place", Program [bumpDef] (Let "y" (int 1) (App (Var "bump") (BorrowMut "y"))), Rejects NotAPlace)
  , ("var dropping a linear value", withToken (LetVar "t" (Con "Token" [] []) (int 1)), Rejects Dropped)
  , ( "linear place used after a move"
    , withToken (LetVar "t" (Con "Token" [] []) (Let "a" (App (Var "consume") (Var "t")) (App (Var "consume") (Var "t"))))
    , Rejects Duplicate
    )
  , ( "changing an outer place inside a handled expression"
    , Program [] (LetVar "x" (int 0) (Handle ioE (Assign "x" (int 1)) [("out", "v", UnitLit), ("putc", "ch", Perform "putc" (Var "ch"))]))
    , Rejects PlaceCapture
    )
  , ( "handler clause reads a place"
    , Program [] (LetVar "x" (int 0) (Handle ioE (Perform "out" (int 1)) [("out", "v", Perform "out" (Var "x")), ("putc", "ch", Perform "putc" (Var "ch"))]))
    , Rejects PlaceCapture
    )
  -- Stage 4 -------------------------------------------------------------------------------
  , ( "polymorphic, effect-polymorphic map"
    , Program [listD, pmapDef, psumDef, incDef] (App (Var "psum") (App (App (TyApp "pmap" [tI, tI] [S.singleton panicE]) (Var "inc")) (plist tI (map int [1, 2, 3]))))
    , ok (VInt i64 9)
    )
  , ( "map over a list of linear tokens"
    , Program
        [listD, pmapDef, psumDef, token, consume]
        (App (Var "psum") (App (App (TyApp "pmap" [tTok, tI] [S.empty]) (Var "consume")) (plist tTok [Con "Token" [] [], Con "Token" [] []])))
    , ok (VInt i64 2)
    )
  , ( "codata interface, two implementations"
    , Program [serialD, loudDef, quietDef, greetDef] (Seq (App (Var "greet") (Var "loud")) (Seq (App (Var "greet") (Var "quiet")) (App (Var "greet") (Var "loud"))))
    , Gives VUnit [72, 105, 72, 105]
    )
  , ("sort with an explicit Ord dictionary", Program [listD, ordD, insertDef, sortDef, ordI64] (sortWith "ordI64"), ok (vlist [1, 2, 3]))
  , ("same sort, another dictionary", Program [listD, ordD, insertDef, sortDef, ordDesc] (sortWith "ordDesc"), ok (vlist [3, 2, 1]))
  , ( "Free type variable at a Free type"
    , Program
        [Def "dup" (TForall [("a", Free)] [] (fn tA (TPair tA tA))) (Lam "x" tA (Pair (Var "x") (Var "x")))]
        (App (TyApp "dup" [tI] []) (int 3))
    , ok (VPair (VInt i64 3) (VInt i64 3))
    )
  , ("+? in range", Program [] (Prim (Arith Optional Add) (int 1) (int 2)), ok (VCon "Some" [VInt i64 3]))
  , ("+? overflow", Program [] (Prim (Arith Optional Add) (IntLit u8 250) (IntLit u8 10)), ok (VCon "None" []))
  , ( "polymorphic recursion"
    , Program
        [ listD
        , Data False "Nested" ["a"] [("Flat", [tA]), ("Nest", [TBox (TData "Nested" [tL tA])])]
        , Def "depth" (TForall [("a", Free)] [] (fnE [panicE, divergeE] (TData "Nested" [tA]) tI)) $
            Lam "n" (TData "Nested" [tA]) $
              Case (Var "n") [("Flat", ["v"], int 1), ("Nest", ["m"], add (int 1) (App (TyApp "depth" [tL tA] []) (Unbox (Var "m"))))]
        ]
        (int 0)
    , Rejects PolyRecursion
    )
  , ( "linear type for a Free variable"
    , Program [token, listD, ordD, insertDef] (Let "g" (TyApp "insert" [tTok] []) (int 0))
    , Rejects KindMismatch
    )
  , ("polymorphic def without type arguments", Program [listD, pmapDef] (Let "g" (Var "pmap") (int 0)), Rejects Mismatch)
  , ( "higher-rank type"
    , Program [Def "hr" (fn (TForall [("a", Lin)] [] (fn tA tA)) tI) (Lam "h" (TForall [("a", Lin)] [] (fn tA tA)) (int 0))] (int 0)
    , Rejects HigherRank
    )
  , ( "linear by default: can't duplicate"
    , Program [Def "dup" (TForall [("a", Lin)] [] (fn tA (TPair tA tA))) (Lam "x" tA (Pair (Var "x") (Var "x")))] (int 0)
    , Rejects Duplicate
    )
  , ( "cocase captures linear"
    , Program [token, consume, serialD] (letTok (Let "s" (Cocase "Serial" [] [("send", Lam "c" tI (Let "r" (App (Var "consume") (Var "t")) UnitLit))]) UnitLit))
    , Rejects LinearCapture
    )
  , ("cocase misses an observation", Program [ordD] (Let "o" (Cocase "Ord" [tI] []) (int 0)), Rejects NonExhaustive)
  , ("negative codata", Program [Codata "Bad" [] [("f", fn (TData "Bad" []) tI)]] (int 0), Rejects NonPositive)
  , ( "negative through a type parameter"
    , Program [Data False "Neg" ["a"] [("Neg", [fn tA tI])], Data False "T" [] [("T", [TBox (TData "Neg" [TData "T" []])])]] (int 0)
    , Rejects NonPositive
    )
  , ( "infinite size through a type parameter"
    , Program [Data False "Wrap" ["a"] [("W", [tA])], Data False "L2" [] [("C2", [tI, TData "Wrap" [TData "L2" []]])]] (int 0)
    , Rejects InfiniteSize
    )
  , ("unbound effect variable", Program [Def "g" (fnE ["'q"] tI tI) (Lam "n" tI (Var "n"))] (int 0), Rejects Unbound)
  ]
