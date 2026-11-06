-- λK₁ big-step call-by-value semantics over environments (spec/core.md §1.4).
open import Keel.Syntax

module Keel.Semantics (Σ : Sig) where

open Sig Σ

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ; _+_; _-_; _*_; _≟_; _<?_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (does)

Tm′ = Tm Σ

data Val : Set where
  int : ℤ → Val
  bool : Bool → Val
  clo : ∀ {n} → Vec Val n → Tm′ (suc n) → Val   -- ⟨ρ, x, e⟩, for λ and λ° alike
  con : (d : Data) (c : Fin (ncon d)) → Vec Val (arity d c) → Val
  box : Val → Val

Env : ℕ → Set
Env = Vec Val

δ : Op Σ → ℤ → ℤ → Val
δ add a b = int (a + b)
δ sub a b = int (a - b)
δ mul a b = int (a * b)
δ eq  a b = bool (does (a ≟ b))
δ lt  a b = bool (does (a <? b))

-- The definitions' bodies. The spec's knot ρ_Σ is unrolled: a reference to f evaluates f's
-- body afresh in the empty environment. Bodies are closed, so this agrees with the knot.
module _ (body : Glob → Tm′ 0) where

  infix 4 _⊢_⇓_ _⊢_⇓*_

  data _⊢_⇓_ {n} (ρ : Env n) : Tm′ n → Val → Set
  data _⊢_⇓*_ {n} (ρ : Env n) : ∀ {k} → Vec (Tm′ n) k → Vec Val k → Set

  data _⊢_⇓_ {n} ρ where
    var   : ∀ {i} → ρ ⊢ var i ⇓ lookup ρ i
    glob  : ∀ {f v} → [] ⊢ body f ⇓ v → ρ ⊢ glob f ⇓ v
    lit   : ∀ {m} → ρ ⊢ lit m ⇓ int m
    tt    : ρ ⊢ tt ⇓ bool true
    ff    : ρ ⊢ ff ⇓ bool false
    op    : ∀ {o e₁ e₂ a b} → ρ ⊢ e₁ ⇓ int a → ρ ⊢ e₂ ⇓ int b → ρ ⊢ op o e₁ e₂ ⇓ δ o a b
    if-t  : ∀ {e e₁ e₂ v} → ρ ⊢ e ⇓ bool true  → ρ ⊢ e₁ ⇓ v → ρ ⊢ if′ e e₁ e₂ ⇓ v
    if-f  : ∀ {e e₁ e₂ v} → ρ ⊢ e ⇓ bool false → ρ ⊢ e₂ ⇓ v → ρ ⊢ if′ e e₁ e₂ ⇓ v
    lam   : ∀ {τ e} → ρ ⊢ lam τ e ⇓ clo ρ e
    llam  : ∀ {τ e} → ρ ⊢ llam τ e ⇓ clo ρ e
    -- function first, then argument
    app   : ∀ {m e₁ e₂ v₂ v} {ρ′ : Env m} {e} → ρ ⊢ e₁ ⇓ clo ρ′ e → ρ ⊢ e₂ ⇓ v₂
          → (v₂ ∷ ρ′) ⊢ e ⇓ v → ρ ⊢ app e₁ e₂ ⇓ v
    let′  : ∀ {e₁ e₂ v₁ v} → ρ ⊢ e₁ ⇓ v₁ → (v₁ ∷ ρ) ⊢ e₂ ⇓ v → ρ ⊢ let′ e₁ e₂ ⇓ v
    con   : ∀ {d c es vs} → ρ ⊢ es ⇓* vs → ρ ⊢ con d c es ⇓ con d c vs
    case  : ∀ {e d alts def c vs b v} → ρ ⊢ e ⇓ con d c vs → alts c ≡ just b
          → (vs ++ ρ) ⊢ b ⇓ v → ρ ⊢ case e d alts def ⇓ v
    case₀ : ∀ {e d alts def c vs e₀ v} → ρ ⊢ e ⇓ con d c vs → alts c ≡ nothing
          → def ≡ just e₀ → ρ ⊢ e₀ ⇓ v → ρ ⊢ case e d alts def ⇓ v
    box′  : ∀ {e v} → ρ ⊢ e ⇓ v → ρ ⊢ box′ e ⇓ box v
    unbox : ∀ {e v} → ρ ⊢ e ⇓ box v → ρ ⊢ unbox e ⇓ v

  -- left to right
  data _⊢_⇓*_ {n} ρ where
    []  : ρ ⊢ [] ⇓* []
    arg : ∀ {k e v} {es : Vec _ k} {vs} → ρ ⊢ e ⇓ v → ρ ⊢ es ⇓* vs → ρ ⊢ (e ∷ es) ⇓* (v ∷ vs)
