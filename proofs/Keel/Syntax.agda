-- λK₁ syntax (spec/core.md §1.1–1.2). Variables are de Bruijn indices; the spec's
-- no-shadowing convention makes the two presentations equivalent.
module Keel.Syntax where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Vec using (Vec)

infixr 7 _⇒_ _⊸_

-- Types over a set D of data-type names.
data Ty (D : Set) : Set where
  int bool : Ty D
  _⇒_      : Ty D → Ty D → Ty D   -- free function
  _⊸_      : Ty D → Ty D → Ty D   -- linear function
  dat      : D → Ty D
  box      : Ty D → Ty D

data Kind : Set where
  free lin : Kind

-- Σ: data declarations, constructor field types, and the types of top-level definitions.
record Sig : Set₁ where
  field
    Data   : Set
    linear : Data → Bool
    ncon   : Data → ℕ
    arity  : (d : Data) → Fin (ncon d) → ℕ
    fields : (d : Data) (c : Fin (ncon d)) → Vec (Ty Data) (arity d c)
    Glob   : Set
    gty    : Glob → Ty Data

module _ (Σ : Sig) where
  open Sig Σ

  κ : Ty Data → Kind
  κ int     = free
  κ bool    = free
  κ (_ ⇒ _) = free
  κ (_ ⊸ _) = lin
  κ (dat d) = if linear d then lin else free
  κ (box τ) = κ τ

  data Op : Set where
    add sub mul eq lt : Op

  data Tm (n : ℕ) : Set where
    var    : Fin n → Tm n
    glob   : Glob → Tm n
    lit    : ℤ → Tm n
    tt ff  : Tm n
    op     : Op → Tm n → Tm n → Tm n
    if′    : Tm n → Tm n → Tm n → Tm n
    lam    : Ty Data → Tm (suc n) → Tm n    -- λ(x:τ). e
    llam   : Ty Data → Tm (suc n) → Tm n    -- λ°(x:τ). e
    app    : Tm n → Tm n → Tm n
    let′   : Tm n → Tm (suc n) → Tm n
    con    : (d : Data) (c : Fin (ncon d)) → Vec (Tm n) (arity d c) → Tm n
    -- Case on data type d: per constructor, a branch binding its fields, or nothing when
    -- the default covers it; then the optional default, which binds nothing.
    case   : Tm n → (d : Data)
           → ((c : Fin (ncon d)) → Maybe (Tm (arity d c + n)))
           → Maybe (Tm n) → Tm n
    box′   : Tm n → Tm n
    unbox  : Tm n → Tm n
