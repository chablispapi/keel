-- | Abstract syntax of Keel Core, stage 1 (spec/core.md §1.1).
module Keel.Syntax where

data Ty
  = TInt
  | TBool
  | TFun Ty Ty   -- ^ τ → σ, free closure
  | TLFun Ty Ty  -- ^ τ ⊸ σ, linear closure
  | TData String
  | TBox Ty
  deriving (Eq, Show)

data Kind = Free | Lin
  deriving (Eq, Show)

data Prim = Add | Sub | Mul | Eq | Lt
  deriving (Eq, Show)

data Term
  = Var String
  | IntLit Integer
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
  deriving (Eq, Show)

data Decl
  = Data Bool String [(String, [Ty])]  -- ^ linear?, name, constructors with field types
  | Def String Ty Term
  deriving (Eq, Show)

data Program = Program [Decl] Term
  deriving (Eq, Show)
