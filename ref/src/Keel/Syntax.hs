-- | Abstract syntax of Keel Core, stages 1–3 (spec/core.md §1.1, §2.1, §3.1).
--
-- Constructors marked /surface/ belong to λK₃ only: "Keel.Elab" removes them before type
-- checking and evaluation, which work on the core.
module Keel.Syntax where

import Data.Set (Set)

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

-- | An effect is a set of labels. Row variables arrive with polymorphism in stage 4.
type Eff = Set String

data Ty
  = TUnit
  | TBool
  | TInt IntTy
  | TFun Ty Eff Ty   -- ^ τ →ε σ, free closure
  | TLFun Ty Eff Ty  -- ^ τ ⊸ε σ, linear closure
  | TData String
  | TBox Ty
  | TPair Ty Ty      -- ^ τ ⊗ σ
  | TRef Ty          -- ^ &τ, surface: only as a parameter type
  | TMut Ty          -- ^ &mut τ, surface: only as a parameter type
  deriving (Eq, Show)

data Kind = Free | Lin
  deriving (Eq, Show)

data Overflow = Checked | Wrap | Saturate
  deriving (Eq, Show)

data ArithOp = Add | Sub | Mul
  deriving (Eq, Show)

data Prim = Arith Overflow ArithOp | Eq | Lt
  deriving (Eq, Show)

data Term
  = Var String
  | UnitLit
  | IntLit IntTy Integer
  | BoolLit Bool
  | Prim Prim Term Term
  | If Term Term Term
  | Lam String Ty Term   -- ^ λ(x:τ). e
  | LLam String Ty Term  -- ^ λ°(x:τ). e
  | App Term Term
  | Let String Term Term
  | Con String [Term]
  | Case Term [(String, [String], Term)]
  | Box Term
  | Unbox Term
  | Perform String Term                     -- ^ op(e)
  | Handle String Term [(String, String, Term)] -- ^ handle e with l { op x → e; … }
  | Pair Term Term                          -- ^ (e, e)
  | LetPair String String Term Term         -- ^ let (x, y) = e in e
  | Assign String Term                      -- ^ x := e, surface
  | Seq Term Term                           -- ^ e; e, surface
  | LetVar String Term Term                 -- ^ var x = e in e, surface
  | Borrow String                           -- ^ &x, surface: only as a function argument
  | BorrowMut String                        -- ^ &mut x, surface: only as a function argument
  deriving (Eq, Show)

-- | Immediate subterms.
children :: Term -> [Term]
children tm = case tm of
  Prim _ a b -> [a, b]
  If c a b -> [c, a, b]
  Lam _ _ b -> [b]
  LLam _ _ b -> [b]
  App f a -> [f, a]
  Let _ e b -> [e, b]
  Con _ as -> as
  Case e alts -> e : [b | (_, _, b) <- alts]
  Box e -> [e]
  Unbox e -> [e]
  Perform _ e -> [e]
  Handle _ e cs -> e : [b | (_, _, b) <- cs]
  Pair a b -> [a, b]
  LetPair _ _ e b -> [e, b]
  Assign _ e -> [e]
  Seq a b -> [a, b]
  LetVar _ e b -> [e, b]
  _ -> []

-- | Apply a function to every immediate subterm.
descend :: (Term -> Term) -> Term -> Term
descend f tm = case tm of
  Prim op a b -> Prim op (f a) (f b)
  If c a b -> If (f c) (f a) (f b)
  Lam x t b -> Lam x t (f b)
  LLam x t b -> LLam x t (f b)
  App g a -> App (f g) (f a)
  Let x e b -> Let x (f e) (f b)
  Con c as -> Con c (map f as)
  Case e alts -> Case (f e) [(c, xs, f b) | (c, xs, b) <- alts]
  Box e -> Box (f e)
  Unbox e -> Unbox (f e)
  Perform op e -> Perform op (f e)
  Handle l e cs -> Handle l (f e) [(op, x, f b) | (op, x, b) <- cs]
  Pair a b -> Pair (f a) (f b)
  LetPair x y e b -> LetPair x y (f e) (f b)
  Assign x e -> Assign x (f e)
  Seq a b -> Seq (f a) (f b)
  LetVar x e b -> LetVar x (f e) (f b)
  _ -> tm

data Decl
  = Data Bool String [(String, [Ty])]  -- ^ linear?, name, constructors with field types
  | Effect String [(String, Ty, Ty)]   -- ^ label, operations with argument and result types
  | Def String Ty Term
  deriving (Eq, Show)

data Program = Program [Decl] Term
  deriving (Eq, Show)

-- | Built-in effect labels. @IO@ has one operation, @out : i64 ⇒ Unit@; the other two have
-- none and cannot be handled.
ioE, panicE, divergeE :: String
ioE = "IO"
panicE = "Panic"
divergeE = "Diverge"
