-- | Abstract syntax of Keel Core, stages 1–2 (spec/core.md §1.1, §2.1).
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
  deriving (Eq, Show)

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
