-- λK₁ declarative typing (spec/core.md §1.2–1.3).
--
-- A context keeps its length under splits so de Bruijn indices mean the same thing in every
-- subterm: a linear binding sent to the other side of a split becomes a hole (nothing).
open import Keel.Syntax

module Keel.Typing (Σ : Sig) where

open Sig Σ

open import Data.Bool using (false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (∃)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; _[_]≔_)
import Data.Vec as Vec
open import Data.Vec.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_)

Ty′ = Ty Data
Tm′ = Tm Σ

Free : Ty′ → Set
Free τ = κ Σ τ ≡ free

-- Well-formedness rule 1 (no hidden resources). Rules 2 and 3 come with Theorem 3.
NoHiddenResources : Set
NoHiddenResources = ∀ d c → linear d ≡ false → All Free (fields d c)

Ctx : ℕ → Set
Ctx = Vec (Maybe Ty′)

FreeEntry : Maybe Ty′ → Set
FreeEntry nothing  = ⊤
FreeEntry (just τ) = Free τ

FreeCtx : ∀ {n} → Ctx n → Set
FreeCtx = All FreeEntry

-- Extend Γ with a constructor's fields (field 0 is variable 0).
bind : ∀ {k n} → Vec Ty′ k → Ctx n → Ctx (k + n)
bind ts Γ = Vec.map just ts ++ Γ

variable
  n k : ℕ
  τ σ : Ty′
  Γ Γ₁ Γ₂ : Ctx n

-- Γ ≔ Γ₁ ⋈ Γ₂: each linear binding goes to exactly one side, free bindings to both.
data _≔_⋈_ : Ctx n → Ctx n → Ctx n → Set where
  []    : [] ≔ [] ⋈ []
  hole  : Γ ≔ Γ₁ ⋈ Γ₂ → (nothing ∷ Γ) ≔ (nothing ∷ Γ₁) ⋈ (nothing ∷ Γ₂)
  share : Free τ → Γ ≔ Γ₁ ⋈ Γ₂ → (just τ ∷ Γ) ≔ (just τ ∷ Γ₁) ⋈ (just τ ∷ Γ₂)
  left  : κ Σ τ ≡ lin → Γ ≔ Γ₁ ⋈ Γ₂ → (just τ ∷ Γ) ≔ (just τ ∷ Γ₁) ⋈ (nothing ∷ Γ₂)
  right : κ Σ τ ≡ lin → Γ ≔ Γ₁ ⋈ Γ₂ → (just τ ∷ Γ) ≔ (nothing ∷ Γ₁) ⋈ (just τ ∷ Γ₂)

opTy : Op Σ → Ty′
opTy add = int
opTy sub = int
opTy mul = int
opTy eq  = bool
opTy lt  = bool

infix 4 _⊢_∶_ _⊢*_∶_

data _⊢_∶_ {n} : Ctx n → Tm′ n → Ty′ → Set
data _⊢*_∶_ {n} : Ctx n → Vec (Tm′ n) k → Vec Ty′ k → Set

-- One constructor's alternative: its branch, or the default covers it.
data Alt {n} (Γ : Ctx n) (σ : Ty′) (d : Data) (def : Maybe (Tm′ n)) (c : Fin (ncon d))
         : Maybe (Tm′ (arity d c + n)) → Set where
  branch  : ∀ {b} → bind (fields d c) Γ ⊢ b ∶ σ → Alt Γ σ d def c (just b)
  -- The default binds nothing, so the fields it drops must be free.
  covered : ∀ {e₀} → def ≡ just e₀ → All Free (fields d c) → Alt Γ σ d def c nothing

-- The default is typed like a branch, and at least one constructor must be left for it.
data Default {n} (Γ : Ctx n) (σ : Ty′) (d : Data)
             (alts : (c : Fin (ncon d)) → Maybe (Tm′ (arity d c + n))) : Maybe (Tm′ n) → Set where
  none : Default Γ σ d alts nothing
  some : ∀ {e₀} → Γ ⊢ e₀ ∶ σ → ∃ (λ c → alts c ≡ nothing) → Default Γ σ d alts (just e₀)

data _⊢_∶_ {n} where
  var   : ∀ {i} → lookup Γ i ≡ just τ → FreeCtx (Γ [ i ]≔ nothing) → Γ ⊢ var i ∶ τ
  glob  : ∀ {f} → FreeCtx Γ → gty f ≡ τ → Γ ⊢ glob f ∶ τ
  lit   : ∀ {m} → FreeCtx Γ → Γ ⊢ lit m ∶ int
  tt    : FreeCtx Γ → Γ ⊢ tt ∶ bool
  ff    : FreeCtx Γ → Γ ⊢ ff ∶ bool
  op    : ∀ {o e₁ e₂} → Γ ≔ Γ₁ ⋈ Γ₂ → Γ₁ ⊢ e₁ ∶ int → Γ₂ ⊢ e₂ ∶ int → Γ ⊢ op o e₁ e₂ ∶ opTy o
  if′   : ∀ {e e₁ e₂} → Γ ≔ Γ₁ ⋈ Γ₂ → Γ₁ ⊢ e ∶ bool → Γ₂ ⊢ e₁ ∶ τ → Γ₂ ⊢ e₂ ∶ τ
        → Γ ⊢ if′ e e₁ e₂ ∶ τ
  lam   : ∀ {e} → FreeCtx Γ → (just τ ∷ Γ) ⊢ e ∶ σ → Γ ⊢ lam τ e ∶ τ ⇒ σ
  llam  : ∀ {e} → (just τ ∷ Γ) ⊢ e ∶ σ → Γ ⊢ llam τ e ∶ τ ⊸ σ
  app   : ∀ {e₁ e₂} → Γ ≔ Γ₁ ⋈ Γ₂ → Γ₁ ⊢ e₁ ∶ τ ⇒ σ → Γ₂ ⊢ e₂ ∶ τ → Γ ⊢ app e₁ e₂ ∶ σ
  lapp  : ∀ {e₁ e₂} → Γ ≔ Γ₁ ⋈ Γ₂ → Γ₁ ⊢ e₁ ∶ τ ⊸ σ → Γ₂ ⊢ e₂ ∶ τ → Γ ⊢ app e₁ e₂ ∶ σ
  let′  : ∀ {e₁ e₂} → Γ ≔ Γ₁ ⋈ Γ₂ → Γ₁ ⊢ e₁ ∶ τ → (just τ ∷ Γ₂) ⊢ e₂ ∶ σ
        → Γ ⊢ let′ e₁ e₂ ∶ σ
  con   : ∀ {d c es} → Γ ⊢* es ∶ fields d c → Γ ⊢ con d c es ∶ dat d
  case  : ∀ {e d alts def} → Γ ≔ Γ₁ ⋈ Γ₂ → Γ₁ ⊢ e ∶ dat d
        → (∀ c → Alt Γ₂ σ d def c (alts c)) → Default Γ₂ σ d alts def
        → Γ ⊢ case e d alts def ∶ σ
  box′  : ∀ {e} → Γ ⊢ e ∶ τ → Γ ⊢ box′ e ∶ box τ
  unbox : ∀ {e} → Γ ⊢ e ∶ box τ → Γ ⊢ unbox e ∶ τ

-- Constructor arguments: Γ₁ ⋈ … ⋈ Γₙ, and Free Γ when there are none.
data _⊢*_∶_ {n} where
  []  : FreeCtx Γ → Γ ⊢* [] ∶ []
  arg : ∀ {k e es} {ts : Vec Ty′ k} → Γ ≔ Γ₁ ⋈ Γ₂ → Γ₁ ⊢ e ∶ τ → Γ₂ ⊢* es ∶ ts
      → Γ ⊢* (e ∷ es) ∶ (τ ∷ ts)

-- A program: every definition checked in the empty context.
Bodies : Set
Bodies = Glob → Tm′ 0

WellTyped : Bodies → Set
WellTyped body = ∀ f → [] ⊢ body f ∶ gty f
