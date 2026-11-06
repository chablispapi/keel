-- Statements of the λK₁ metatheory (spec/core.md §1.5). Postulated: no proofs yet.
open import Keel.Syntax

module Keel.Theorems (Σ : Sig) where

open Sig Σ

open import Data.Maybe using (just; nothing)
open import Data.Vec using (Vec; []; _∷_)

open import Keel.Typing Σ
open import Keel.Semantics Σ

infix 4 ⊨_∶_ _⊨*_

-- Value and environment typing (the "extend typing to values" of Theorem 1's sketch).
data ⊨_∶_ : Val → Ty′ → Set
data _⊨*_ : ∀ {n} → Vec Val n → Ctx n → Set
data ⊨fields : ∀ {k} → Vec Val k → Vec Ty′ k → Set

data ⊨_∶_ where
  int  : ∀ {m} → ⊨ int m ∶ int
  bool : ∀ {b} → ⊨ bool b ∶ bool
  clo⇒ : ∀ {n τ σ} {ρ : Env n} {Γ e} → ρ ⊨* Γ → FreeCtx Γ → (just τ ∷ Γ) ⊢ e ∶ σ
       → ⊨ clo ρ e ∶ τ ⇒ σ
  clo⊸ : ∀ {n τ σ} {ρ : Env n} {Γ e} → ρ ⊨* Γ → (just τ ∷ Γ) ⊢ e ∶ σ → ⊨ clo ρ e ∶ τ ⊸ σ
  con  : ∀ {d c vs} → ⊨fields vs (fields d c) → ⊨ con d c vs ∶ dat d
  box  : ∀ {v τ} → ⊨ v ∶ τ → ⊨ box v ∶ box τ

-- A hole may hold any value: it is a linear binding the other side of a split owns.
data _⊨*_ where
  []   : [] ⊨* []
  hole : ∀ {n v} {ρ : Env n} {Γ} → ρ ⊨* Γ → (v ∷ ρ) ⊨* (nothing ∷ Γ)
  bound : ∀ {n v τ} {ρ : Env n} {Γ} → ⊨ v ∶ τ → ρ ⊨* Γ → (v ∷ ρ) ⊨* (just τ ∷ Γ)

data ⊨fields where
  []  : ⊨fields [] []
  _∷_ : ∀ {k v τ} {vs : Vec Val k} {ts} → ⊨ v ∶ τ → ⊨fields vs ts → ⊨fields (v ∷ vs) (τ ∷ ts)

-- Theorem 1 (type soundness), preservation half: evaluation keeps types.
-- ponytail: the "never stuck" half needs a fuel-indexed evaluator (stuck ≠ timeout);
-- add it when proving, the big-step relation can't tell stuck from diverging.
postulate
  preservation : ∀ {n} {body : Bodies} {Γ : Ctx n} {ρ : Env n} {e τ v}
    → NoHiddenResources → WellTyped body
    → Γ ⊢ e ∶ τ → ρ ⊨* Γ → _⊢_⇓_ body ρ e v → ⊨ v ∶ τ

-- Theorem 2 (linearity) needs evaluation that tracks linear identities; Theorem 3 (finite
-- layout) needs well-formedness rule 2. Neither is stated yet.
