-- | Abstract syntax of Keel Core, stages 1–4 (spec/core.md §1.1, §2.1, §3.1, §4.1).
--
-- Constructors marked /surface/ belong to λK₃ only: "Keel.Elab" removes them before type
-- checking and evaluation, which work on the core.
module Keel.Syntax where

import Data.List (elemIndex, intercalate)
import Data.Maybe (fromMaybe)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S

-- | Fixed-width integer types.
data IntTy = IntTy {signed :: Bool, bits :: Int}
  deriving (Eq, Ord, Show)

i8, i16, i32, i64, u8, u16, u32, u64 :: IntTy
i8 = IntTy True 8
i16 = IntTy True 16
i32 = IntTy True 32
i64 = IntTy True 64
u8 = IntTy False 8
u16 = IntTy False 16
u32 = IntTy False 32
u64 = IntTy False 64

-- | Smallest and largest value of an integer type.
intRange :: IntTy -> (Integer, Integer)
intRange (IntTy sgn n)
  | sgn = (-(2 ^ (n - 1)), 2 ^ (n - 1) - 1)
  | otherwise = (0, 2 ^ n - 1)

-- | An effect is a set of labels. Effect variables (ρ) are labels starting with @'@; they are
-- bound by ∀ and replaced by effect sets on instantiation (§4.1).
type Eff = Set String

isEffVar :: String -> Bool
isEffVar ('\'' : _) = True
isEffVar _ = False

data Ty
  = TUnit
  | TBool
  | TInt IntTy
  | TFun Ty Eff Ty   -- ^ τ →ε σ, free closure
  | TLFun Ty Eff Ty  -- ^ τ ⊸ε σ, linear closure
  | TData String [Ty] -- ^ data or codata type applied to type arguments
  | TVar String
  | TBox Ty
  | TPair Ty Ty      -- ^ τ ⊗ σ
  | TForall [(String, Kind)] [String] Ty -- ^ ∀ types and effect variables; only at the top of a def's type
  | TRef Ty          -- ^ &τ, surface: only as a parameter type
  | TMut Ty          -- ^ &mut τ, surface: only as a parameter type
  | TMeta Int        -- ^ inference variable, front end only ("Keel.Infer"); -1 is an unfilled hole
  deriving (Eq, Show)

data Kind = Free | Lin
  deriving (Eq, Show)

data Overflow = Checked | Wrap | Saturate | Optional -- ^ Optional: @+?@ returns Option
  deriving (Eq, Show)

-- | Division truncates toward zero; @Rem@ has the sign of the dividend. Only the checked forms
-- exist: dividing by zero, and @min / -1@, panic.
data ArithOp = Add | Sub | Mul | Div | Rem
  deriving (Eq, Show)

-- | Bitwise operations: never overflow; shifts are logical for unsigned types and
-- arithmetic for signed ones, and a left shift wraps to the width.
data BitOp = And | Or | Xor | Shl | Shr
  deriving (Eq, Show)

data Prim = Arith Overflow ArithOp | Bits BitOp | Eq | Lt
  deriving (Eq, Show)

-- | Operations on the built-in @Array a@ (M5): a growable array of one-word elements, updated
-- in place when the array is not shared and copied when it is (spec/memory.md).
-- AArena is not an array operation but is built in the same way: @arena (\u. e)@ evaluates e
-- and frees everything e allocated at once (spec/memory.md, "Arenas").
data ArrayOp = AEmpty | ANew | ALength | AGet | ASet | APush | APop | AArena
  deriving (Eq, Show)

-- | The names array operations are written with, applied to all their arguments
-- (@arrayGet xs 3@, or just @arrayEmpty@); "std.array" wraps them as ordinary functions.
arrayOps :: [(String, ArrayOp)]
arrayOps = [("arrayEmpty", AEmpty), ("arrayNew", ANew), ("arrayLength", ALength), ("arrayGet", AGet), ("arraySet", ASet), ("arrayPush", APush), ("arrayPop", APop), ("arena", AArena)]

-- | An array operation's argument types, result type and effects, for element type @a@
-- (which must be Free: the elements are copied in and out).
arrayOpType :: ArrayOp -> Ty -> ([Ty], Ty, Eff)
arrayOpType op a = case op of
  AEmpty -> ([], arr, S.empty)
  ANew -> ([TInt i64, a], arr, panic)
  ALength -> ([arr], TInt i64, S.empty)
  AGet -> ([arr, TInt i64], a, panic)
  ASet -> ([arr, TInt i64, a], arr, panic)
  APush -> ([arr, a], arr, S.empty)
  APop -> ([arr], arr, panic)
  AArena -> ([TFun TUnit S.empty a], a, S.empty) -- only its arity and result: typed as f ()
  where
    arr = TData "Array" [a]
    panic = S.singleton panicE

data Term
  = Var String
  | UnitLit
  | IntLit IntTy Integer
  | NumLit (Maybe Ty) Integer -- ^ literal whose width is inferred, front end only
  | Convert IntTy Term        -- ^ e as ι: wrapping conversion between integer types
  | BoolLit Bool
  | Prim Prim Term Term
  | ArrayPrim ArrayOp Ty [Term] -- ^ an array operation at an element type, applied to all its arguments
  | If Term Term Term
  | Lam String Ty Term   -- ^ λ(x:τ). e
  | LLam String Ty Term  -- ^ λ°(x:τ). e
  | App Term Term
  | Let String Term Term
  | Con String [Ty] [Term]                  -- ^ C[τ̄](e, …)
  | Case Term [(String, [String], Term)]
  | Box Term
  | Unbox Term
  | Perform String Term                     -- ^ op(e)
  | Handle String Term [(String, String, Term)] -- ^ handle e with l { op x → e; … }
  | Pair Term Term                          -- ^ (e, e)
  | LetPair String String Term Term         -- ^ let (x, y) = e in e
  | TyApp String [Ty] [Eff]                 -- ^ f[τ̄; ε̄], instantiate a polymorphic def
  | Cocase String [Ty] [(String, Term)]     -- ^ cocase D[τ̄] { obs → e; … }
  | Proj Term String                        -- ^ e.obs
  | Assign String Term                      -- ^ x := e, surface
  | Seq Term Term                           -- ^ e; e, surface
  | LetVar String Term Term                 -- ^ var x = e in e, surface
  | Borrow String                           -- ^ &x, surface: only as a function argument
  | BorrowMut String                        -- ^ &mut x, surface: only as a function argument
  | BitsLit String [(String, Term)]         -- ^ Status { field = e, … }, bitdata value, front end only
  | At Pos Term                             -- ^ source position of the term; stripped before optimization
  deriving (Eq, Show)

-- | A source position: file, line and column.
type Pos = (FilePath, Int, Int)

-- | A parsed source file: its imports (module name, the qualifier it is known by, and where),
-- its declarations (with a @private@ flag), and its @main@ if it has one.
-- | One source file. 'modSites' is where each declared name (type, constructor, operation,
-- definition) is written, for the language server's go-to-definition.
data Module = Module {modImports :: [(String, String, Pos)], modDecls :: [(Bool, Decl)], modMain :: Maybe Term, modSites :: [(String, Pos)]}

-- | Remove source positions.
stripAt :: Term -> Term
stripAt (At _ e) = stripAt e
stripAt tm = descend stripAt tm

-- | Immediate subterms.
children :: Term -> [Term]
children tm = case tm of
  Prim _ a b -> [a, b]
  ArrayPrim _ _ as -> as
  If c a b -> [c, a, b]
  Lam _ _ b -> [b]
  LLam _ _ b -> [b]
  App f a -> [f, a]
  Let _ e b -> [e, b]
  Con _ _ as -> as
  Case e alts -> e : [b | (_, _, b) <- alts]
  Box e -> [e]
  Unbox e -> [e]
  Perform _ e -> [e]
  Handle _ e cs -> e : [b | (_, _, b) <- cs]
  Pair a b -> [a, b]
  LetPair _ _ e b -> [e, b]
  Cocase _ _ bs -> map snd bs
  Proj e _ -> [e]
  Convert _ e -> [e]
  Assign _ e -> [e]
  Seq a b -> [a, b]
  LetVar _ e b -> [e, b]
  At _ e -> [e]
  _ -> []

-- | Apply a function to every immediate subterm.
descend :: (Term -> Term) -> Term -> Term
descend f tm = case tm of
  Prim op a b -> Prim op (f a) (f b)
  ArrayPrim op t as -> ArrayPrim op t (map f as)
  If c a b -> If (f c) (f a) (f b)
  Lam x t b -> Lam x t (f b)
  LLam x t b -> LLam x t (f b)
  App g a -> App (f g) (f a)
  Let x e b -> Let x (f e) (f b)
  Con c ts as -> Con c ts (map f as)
  Case e alts -> Case (f e) [(c, xs, f b) | (c, xs, b) <- alts]
  Box e -> Box (f e)
  Unbox e -> Unbox (f e)
  Perform op e -> Perform op (f e)
  Handle l e cs -> Handle l (f e) [(op, x, f b) | (op, x, b) <- cs]
  Pair a b -> Pair (f a) (f b)
  LetPair x y e b -> LetPair x y (f e) (f b)
  Cocase d ts bs -> Cocase d ts [(o, f b) | (o, b) <- bs]
  Proj e o -> Proj (f e) o
  Convert t e -> Convert t (f e)
  Assign x e -> Assign x (f e)
  Seq a b -> Seq (f a) (f b)
  LetVar x e b -> LetVar x (f e) (f b)
  At p e -> At p (f e)
  _ -> tm

-- | Monadic 'descend': rewrite every immediate subterm, left to right.
descendM :: (Monad m) => (Term -> m Term) -> Term -> m Term
descendM f tm = case tm of
  Prim op a b -> Prim op <$> f a <*> f b
  ArrayPrim op t as -> ArrayPrim op t <$> mapM f as
  If c a b -> If <$> f c <*> f a <*> f b
  Lam x t b -> Lam x t <$> f b
  LLam x t b -> LLam x t <$> f b
  App g a -> App <$> f g <*> f a
  Let x e b -> Let x <$> f e <*> f b
  Con c ts as -> Con c ts <$> mapM f as
  Case e alts -> Case <$> f e <*> mapM (\(c, xs, b) -> (c,xs,) <$> f b) alts
  Box e -> Box <$> f e
  Unbox e -> Unbox <$> f e
  Perform op e -> Perform op <$> f e
  Handle l e cs -> Handle l <$> f e <*> mapM (\(op, x, b) -> (op,x,) <$> f b) cs
  Pair a b -> Pair <$> f a <*> f b
  LetPair x y e b -> LetPair x y <$> f e <*> f b
  Cocase d ts bs -> Cocase d ts <$> mapM (\(o, b) -> (o,) <$> f b) bs
  Proj e o -> (`Proj` o) <$> f e
  Convert t e -> Convert t <$> f e
  Assign x e -> Assign x <$> f e
  Seq a b -> Seq <$> f a <*> f b
  LetVar x e b -> LetVar x <$> f e <*> f b
  At p e -> At p <$> f e
  _ -> pure tm

-- | All subterms, including the term itself.
universe :: Term -> [Term]
universe tm = tm : concatMap universe (children tm)

-- Substitution ----------------------------------------------------------------------------

type TySubst = M.Map String Ty

type EffSubst = M.Map String Eff

substEff :: EffSubst -> Eff -> Eff
substEff ev e = S.unions [M.findWithDefault (S.singleton l) l ev | l <- S.toList e]

substTy :: TySubst -> EffSubst -> Ty -> Ty
substTy tv ev t = case t of
  TVar a -> M.findWithDefault t a tv
  TFun a e b -> TFun (go a) (substEff ev e) (go b)
  TLFun a e b -> TLFun (go a) (substEff ev e) (go b)
  TData d as -> TData d (map go as)
  TBox a -> TBox (go a)
  TPair a b -> TPair (go a) (go b)
  TRef a -> TRef (go a)
  TMut a -> TMut (go a)
  TForall vs es b -> TForall vs es (substTy (foldr (M.delete . fst) tv vs) (foldr M.delete ev es) b)
  _ -> t
  where
    go = substTy tv ev

-- | Substitute in every type annotation of a term.
substTerm :: TySubst -> EffSubst -> Term -> Term
substTerm tv ev = go
  where
    st = substTy tv ev
    go tm = descend go $ case tm of
      Lam x t b -> Lam x (st t) b
      LLam x t b -> LLam x (st t) b
      Con c ts as -> Con c (map st ts) as
      ArrayPrim op t as -> ArrayPrim op (st t) as
      TyApp f ts es -> TyApp f (map st ts) (map (substEff ev) es)
      Cocase d ts bs -> Cocase d (map st ts) bs
      _ -> tm

-- Printing --------------------------------------------------------------------------------

prettyTy :: Ty -> String
prettyTy t = case t of
  TUnit -> "Unit"
  TBool -> "Bool"
  TInt (IntTy s n) -> (if s then "i" else "u") ++ show n
  TFun a e b -> paren a ++ " →" ++ prettyEff e ++ " " ++ prettyTy b
  TLFun a e b -> paren a ++ " ⊸" ++ prettyEff e ++ " " ++ prettyTy b
  TData d [] -> d
  TData d as -> d ++ "[" ++ intercalate ", " (map prettyTy as) ++ "]"
  TVar a -> a
  TBox a -> "Box " ++ paren a
  TPair a b -> paren a ++ " ⊗ " ++ paren b
  TForall vs es b -> "∀" ++ unwords (map fst vs ++ es) ++ ". " ++ prettyTy b
  TRef a -> "&" ++ paren a
  TMut a -> "&mut " ++ paren a
  TMeta n -> "?" ++ show n
  where
    paren x = case x of
      TFun {} -> "(" ++ prettyTy x ++ ")"
      TLFun {} -> "(" ++ prettyTy x ++ ")"
      TPair {} -> "(" ++ prettyTy x ++ ")"
      _ -> prettyTy x

prettyEff :: Eff -> String
prettyEff e
  | S.null e = ""
  | otherwise = "{" ++ intercalate ", " (S.toList e) ++ "}"

-- Declarations ----------------------------------------------------------------------------

data Decl
  = Data Bool String [String] [(String, [Ty])] -- ^ linear?, name, type parameters, constructors
  | Codata String [String] [(String, Ty)]      -- ^ name, type parameters, observations
  | Effect String [(String, Ty, Ty)]           -- ^ label, operations with argument and result types
  | Def String Ty Term
  | Bitdata String IntTy [(String, Int, Int)] -- ^ name, underlying integer, fields (low bit, width); front end only
  deriving (Eq, Show)

data Program = Program [Decl] Term
  deriving (Eq, Show)

-- | Built-in effect labels. @IO@ (output), @Input@, @MMIO@, @Files@ and @Net@ have the
-- operations in 'builtinEffects'; @Panic@ and @Diverge@ have none and cannot be handled.
ioE, inputE, mmioE, filesE, netE, panicE, divergeE :: String
ioE = "IO"
inputE = "Input"
filesE = "Files"
netE = "Net"
mmioE = "MMIO"
panicE = "Panic"
divergeE = "Diverge"

-- | Built-in effects and their operations, in operation-number order (the native runtime
-- numbers operations this way, then user operations in declaration order). Unhandled, @out@
-- prints a number and a newline, @putc@ one byte, @getc@ reads one byte of input (-1 at its
-- end), the MMIO operations access device memory (freestanding targets only), and the Files
-- operations read and write files: @openFile@ takes a path's bytes and gives a handle to read
-- (-1 if it can't be opened), @readByte@ a byte (-1 at the end); @createFile@ (emptied) and
-- @appendFile@ give one to write, @writeBytes@ writes bytes (how many, or -1); @closeFile@
-- releases a handle (hosted targets only). "std.file" wraps them. The Net operations are thin socket calls on IPv4 TCP (hosted
-- targets only; elsewhere they fail): "std.loop" builds its event loop on them.
builtinEffects :: [(String, [(String, Ty, Ty)])]
builtinEffects =
  [ (ioE, [("out", TInt i64, TUnit), ("putc", TInt u8, TUnit)])
  , (inputE, [("getc", TUnit, TInt i64)])
  , ( mmioE
    , [ ("read8", TInt u64, TInt u8)
      , ("read32", TInt u64, TInt u32)
      , ("write8", TPair (TInt u64) (TInt u8), TUnit)
      , ("write32", TPair (TInt u64) (TInt u32), TUnit)
      ]
    )
  , ( filesE
    , [ ("openFile", TData "Array" [TInt u8], TInt i64)
      , ("readByte", TInt i64, TInt i64)
      , ("closeFile", TInt i64, TUnit)
      , ("createFile", TData "Array" [TInt u8], TInt i64)
      , ("appendFile", TData "Array" [TInt u8], TInt i64)
      , ("writeBytes", TPair (TInt i64) (TData "Array" [TInt u8]), TInt i64)
      ]
    )
  , ( netE
    , [ ("tcpListen", TPair (TInt u32) (TInt u16), TInt i64) -- address (0: any), port (0: any free) → fd or -1
      , ("sockPort", TInt i64, TInt i64) -- a listener's port
      , ("tcpAccept", TInt i64, TInt i64) -- a waiting connection's fd, or -1
      , ("tcpConnect", TPair (TInt u32) (TInt u16), TInt i64) -- fd or -1
      , ("sockSend", TPair (TInt i64) (TPair (TData "Array" [TInt u8]) (TInt i64)), TInt i64) -- (fd, (bytes, from)): how many it took without waiting, or -1
      , ("sockRecv", TInt i64, TData "Array" [TInt u8]) -- what has arrived; empty: closed
      , ("sockClose", TInt i64, TUnit)
      , ("pollWait", TPair (TData "Array" [TInt i32]) (TInt i64), TInt i64) -- fd · 4 + 1 (read) + 2 (write), timeout in ms (-1: none) → index · 4 + readable + 2 · writable, -1 (timed out), or -2 (can't wait)
      , ("clockMs", TUnit, TInt i64) -- milliseconds, monotonic
      ]
    )
  ]

-- | A built-in operation's number: its place in 'builtinEffects' (user operations follow).
opNumber :: String -> Int
opNumber op = fromMaybe (error ("not a built-in operation: " ++ op)) (elemIndex op [o | (_, os) <- builtinEffects, (o, _, _) <- os])

-- | The Net operations, in order: the last built-in operations (the runtimes dispatch on
-- @>= opNumber "tcpListen"@).
netOpNames :: [String]
netOpNames = [o | (l, os) <- builtinEffects, l == netE, (o, _, _) <- os]

-- | Built-in data: @data Option a = None | Some(a)@, the result of @+?@.
optionDecl :: Decl
optionDecl = Data False "Option" ["a"] [("None", []), ("Some", [TVar "a"])]

-- | Built-in data: @Array a@, with no constructors (see 'ArrayOp'). Declared so kinds work as
-- for any data type: an array is linear if its elements are.
arrayDecl :: Decl
arrayDecl = Data False "Array" ["a"] []
