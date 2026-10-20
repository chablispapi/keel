# Keel Core: specification

Keel Core is the small calculus that every part of Keel elaborates into: the surface language,
the REPL and the compiler. It is built in four stages, each extending the previous one:

| Stage | Calculus | Adds | Status |
|---|---|---|---|
| 1 | λK₁ | Linear types, functions, `data`, `case`, `Box` | **this document** |
| 2 | λK₂ | Effect rows, tail-resumptive handlers, `Panic`, checked arithmetic | planned |
| 3 | λK₃ | Second-class references `&` / `&mut`, elaborated to state passing | planned |
| 4 | λK₄ | `codata`, rank-1 polymorphism, monomorphization | planned |

The executable reference checker and evaluator live in `ref/` (Haskell). Every rule below
corresponds to a case in `ref/src/Keel/Check.hs` or `ref/src/Keel/Eval.hs`, and the examples in
§1.6 are the tests in `ref/test/Main.hs`.

---

## 1. λK₁: linear λ-calculus with data

### 1.1 Syntax

```
τ ::= Int | Bool                      base types
    | τ → τ                           free function (captures no linear values)
    | τ ⊸ τ                           linear function (may capture linear values; call once)
    | D                               user data type
    | Box τ                           heap indirection

e ::= x | n | true | false
    | e ⊕ e                           ⊕ ∈ { +, -, *, ==, < }
    | if e then e else e
    | λ(x:τ). e                       free closure      : τ → σ
    | λ°(x:τ). e                      linear closure    : τ ⊸ σ
    | e e
    | let x = e in e
    | C(e₁, …, eₙ)                    constructor
    | case e of { C(x₁, …, xₙ) → e ; … }
    | box e | unbox e

decl    ::= [linear] data D = C₁(τ, …) | … | Cₙ(τ, …)
          | def f : τ = e             top-level, may be recursive
program ::= decl* main e
```

Surface syntax writes `⊸` as `-o`. In this stage, `Int` is a mathematical integer; stage 2 gives
integers fixed widths and checked overflow.

**Conventions.** Bound variables are distinct from each other and from top-level names (no
shadowing); the surface language renames before elaborating into Keel Core. Σ is the
signature: the data declarations, the constructor types `C : (τ₁, …, τₙ) → D`, and the
top-level definitions `f : τ`.

### 1.2 Kinds: which types are linear

Every type has a kind, `Free` (may be copied and dropped) or `Lin` (must be used exactly once):

```
κ(Int) = κ(Bool) = Free
κ(τ → σ)  = Free
κ(τ ⊸ σ)  = Lin
κ(Box τ)  = κ(τ)
κ(D)      = Lin   if D is declared `linear data`
          = Free  otherwise
```

**Design note: linearity belongs to types, not arrows.** This follows Austral and Rust rather
than Linear Haskell. A firmware resource (a hardware handle or a DMA token) is always linear,
so its type says so once, instead of every function taking it having to write `⊸`. Here `⊸`
marks a *closure* that captured linear values and so can be called only once. Whether a
function consumes its argument follows from the argument's type.

> This refines the informal reading in `notes.md`, where `List a -o List b` meant "consumes the
> list". Under this design a `Free` list may be copied; guaranteed in-place reuse comes from
> `linear data` or from the reuse analysis in milestone M2.

**Well-formed data declarations:**

1. *(no hidden resources)* every field type of a non-linear `data D` has kind `Free`. A free
   value can't contain a linear one, or copying it would copy the resource.
2. *(finite size)* a data type may not contain itself, directly or through other data types,
   except behind `Box`. Every value then has a statically known size, which the compiler needs
   for unboxed layouts.
3. All named types exist, and constructor names are globally unique.

### 1.3 Typing

**Declarative rules.** The judgment `Γ ⊢ e : τ` means "under local context Γ, `e` has type `τ`
and uses every linear variable of Γ exactly once". The signature Σ is implicit; its names are
always available and are `Free`.

- `Free(Γ)` means every binding in Γ has a `Free` type.
- `Γ₁ ⋈ Γ₂` is a *split*: each linear binding goes to exactly one side, and free bindings go
  to both.

There is no weakening and no contraction for linear bindings. That is the whole linearity
discipline.

```
            Free(Γ)                        Free(Γ)     (f : τ) ∈ Σ
 (Var) ─────────────────          (Glob) ──────────────────────
         Γ, x:τ ⊢ x : τ                       Γ ⊢ f : τ

            Free(Γ)                         Γ₁ ⊢ e₁ : Int    Γ₂ ⊢ e₂ : Int
 (Int) ─────────────────          (Op)  ──────────────────────────────────────  (Bool for == <)
         Γ ⊢ n : Int                          Γ₁ ⋈ Γ₂ ⊢ e₁ ⊕ e₂ : Int

         Γ₁ ⊢ e : Bool    Γ₂ ⊢ e₁ : τ    Γ₂ ⊢ e₂ : τ
 (If)  ───────────────────────────────────────────────      both branches use the same Γ₂
           Γ₁ ⋈ Γ₂ ⊢ if e then e₁ else e₂ : τ

         Γ, x:τ ⊢ e : σ     Free(Γ)                       Γ, x:τ ⊢ e : σ
 (Lam) ───────────────────────────          (LLam) ─────────────────────────
         Γ ⊢ λ(x:τ). e : τ → σ                       Γ ⊢ λ°(x:τ). e : τ ⊸ σ

         Γ₁ ⊢ e₁ : τ ⇒ σ    Γ₂ ⊢ e₂ : τ                     ⇒ ∈ { →, ⊸ }
 (App) ──────────────────────────────────
              Γ₁ ⋈ Γ₂ ⊢ e₁ e₂ : σ

         Γ₁ ⊢ e₁ : τ    Γ₂, x:τ ⊢ e₂ : σ
 (Let) ──────────────────────────────────
         Γ₁ ⋈ Γ₂ ⊢ let x = e₁ in e₂ : σ

         C : (τ₁, …, τₙ) → D ∈ Σ     Γᵢ ⊢ eᵢ : τᵢ  (i = 1..n)
 (Con) ───────────────────────────────────────────────────────
              Γ₁ ⋈ … ⋈ Γₙ ⊢ C(e₁, …, eₙ) : D

         Γ₁ ⊢ e : D      D = C₁(τ̄₁) | … | Cₖ(τ̄ₖ)      Γ₂, x̄ᵢ:τ̄ᵢ ⊢ eᵢ : σ  (each Cᵢ exactly once)
 (Case) ─────────────────────────────────────────────────────────────────────────────────────
              Γ₁ ⋈ Γ₂ ⊢ case e of { C₁(x̄₁) → e₁ ; … ; Cₖ(x̄ₖ) → eₖ } : σ

          Γ ⊢ e : τ                       Γ ⊢ e : Box τ
 (Box) ──────────────────       (Unbox) ─────────────────
        Γ ⊢ box e : Box τ                 Γ ⊢ unbox e : τ
```

A top-level definition `def f : τ = e` is well typed when `· ⊢ e : τ`. Definitions are checked
in an empty local context, so they never capture anything; recursion goes through (Glob).
A program is well typed when every declaration is well formed and `· ⊢ main : τ` for some τ.

**Algorithmic rules (what `Check.hs` implements).** Splitting contexts is not syntax-directed,
so the checker computes usage instead. `Γ ⊢ e ⇒ τ ▷ U` synthesizes τ together with the set U of
linear variables of Γ that `e` uses:

| Construct | Usage | Rejected with |
|---|---|---|
| `x` with κ(Γ(x)) = Lin | `{x}` | |
| `x` free, literal, global | `∅` | |
| two subterms used together (app, op, let, con, scrutinee + branches) | `U₁ ∪ U₂`, requires `U₁ ∩ U₂ = ∅` | `Duplicate` |
| `if` / `case` branches | all branches must have equal U | `BranchMismatch` |
| binder `x:τ` with κ(τ) = Lin (λ, let, pattern) | requires `x ∈ U_body`, then `U_body ∖ {x}` | `Dropped` |
| `λ(x:τ). e` (free closure) | requires `U_body ∖ {x} = ∅` | `LinearCapture` |
| `λ°(x:τ). e` | `U_body ∖ {x}` (captured linear values) | |

Other errors: `Mismatch` (types differ), `Unbound`, `Shadowing`, `NonExhaustive` (case misses or
repeats a constructor), `LinearField` (rule 1), `InfiniteSize` (rule 2), `BadDecl` (duplicate
or unknown names).

*Correspondence (sketch).* `Γ ⊢ e ⇒ τ ▷ U` holds exactly when `Γ|free, U ⊢ e : τ` is derivable
declaratively, where `Γ|free` is the free part of Γ and U names the linear bindings kept. By
induction on `e`: disjointness of usage sets is exactly the existence of a split; equal branch
usage is the shared Γ₂ of (If)/(Case); and the binder checks are the absence of weakening.

### 1.4 Operational semantics

Call-by-value, big-step, over environments. No substitution is performed (see `notes.md` §5).

```
v ::= n | true | false | ⟨ρ, x, e⟩ | C(v₁, …, vₙ) | box v        values
ρ ::= x₁ ↦ v₁, …, xₙ ↦ vₙ                                       environments
```

The global environment ρ_Σ maps every `def f = e` to the value of `e` in ρ_Σ itself, which is
a recursive knot: definitions are closures, so this is well-founded. Every evaluation runs in
an extension of ρ_Σ.

```
 ρ ⊢ x ⇓ ρ(x)        ρ ⊢ n ⇓ n        ρ ⊢ λ(x:τ). e ⇓ ⟨ρ, x, e⟩        ρ ⊢ λ°(x:τ). e ⇓ ⟨ρ, x, e⟩

 ρ ⊢ e₁ ⇓ ⟨ρ', x, e⟩    ρ ⊢ e₂ ⇓ v₂    ρ', x ↦ v₂ ⊢ e ⇓ v          (function first, then argument)
 ──────────────────────────────────────────────────────────
                    ρ ⊢ e₁ e₂ ⇓ v

 ρ ⊢ e₁ ⇓ v₁    ρ, x ↦ v₁ ⊢ e₂ ⇓ v           ρ ⊢ e₁ ⇓ n₁    ρ ⊢ e₂ ⇓ n₂
 ──────────────────────────────────           ───────────────────────────────
      ρ ⊢ let x = e₁ in e₂ ⇓ v                  ρ ⊢ e₁ ⊕ e₂ ⇓ n₁ ⊕ n₂

 ρ ⊢ e ⇓ true    ρ ⊢ e₁ ⇓ v                  ρ ⊢ e ⇓ false    ρ ⊢ e₂ ⇓ v
 ─────────────────────────────────            ─────────────────────────────────
  ρ ⊢ if e then e₁ else e₂ ⇓ v                  ρ ⊢ if e then e₁ else e₂ ⇓ v

 ρ ⊢ eᵢ ⇓ vᵢ  (left to right)                 ρ ⊢ e ⇓ Cⱼ(v̄)    ρ, x̄ⱼ ↦ v̄ ⊢ eⱼ ⇓ v
 ────────────────────────────────              ──────────────────────────────────────────
  ρ ⊢ C(e₁, …, eₙ) ⇓ C(v₁, …, vₙ)               ρ ⊢ case e of { …; Cⱼ(x̄ⱼ) → eⱼ; … } ⇓ v

 ρ ⊢ e ⇓ v                   ρ ⊢ e ⇓ box v
 ─────────────────────        ──────────────────
  ρ ⊢ box e ⇓ box v            ρ ⊢ unbox e ⇓ v
```

Linearity is purely static: λ and λ° evaluate identically, and kinds are erased.

### 1.5 Metatheory

**Theorem 1 (type soundness).** If `⊢ program` and `· ⊢ main : τ`, then evaluation of `main`
never gets stuck: every rule's premises about the shape of values hold (an application meets a
closure, `case` meets a constructor of D with a matching branch, `⊕` meets integers), and if
`main ⇓ v` then `⊢ v : τ`.

*Sketch.* Extend typing to values and environments: `⊢ ⟨ρ, x, e⟩ : τ ⇒ σ` when `⊢ ρ : Γ` and
`Γ, x:τ ⊢ e : σ`; `⊢ ρ : Γ` when every `ρ(y)` has type `Γ(y)`. Prove by induction on the
evaluation derivation that `⊢ ρ : Γ`, `Γ ⊢ e : τ` and `ρ ⊢ e ⇓ v` imply `⊢ v : τ`. The global
knot is handled by assuming `⊢ ρ_Σ : Σ` coinductively; it holds because every definition is
checked in the empty context. Exhaustive `case` and canonical forms (a value of type `D` is a
constructor of `D`; of function type, a closure) give progress. Big-step semantics doesn't
describe divergence; recursion may diverge in this stage. Stage 2's `Diverge` effect makes
that visible in types.

**Theorem 2 (linearity: no duplication, no loss).** Give each value of a `Lin` type created
during evaluation a unique identity. In the evaluation of a well-typed program, every such
identity is consumed (matched by `case`, called as a λ° closure, or passed on into exactly one
other value or binding) exactly once along the executed path. It is never copied and never
silently dropped.

*Sketch.* Typing has no weakening or contraction for `Lin` bindings, and splits send each
linear binding to exactly one subterm. A free value can't contain a linear one (well-formedness
rule 1), and a free closure can't capture one (rule Lam), so copying a free value never copies
a resource. By induction on evaluation, the multiset of live linear identities stays in
one-to-one correspondence with the linear bindings in the current context.

**Theorem 3 (finite layout).** For every well-formed data type `D`, the size of an unboxed `D`
value is bounded: the largest constructor's fields, with each `Box` counted as one pointer.
This follows directly from rule 2.

### 1.6 Examples

Each example is a test case in `ref/test/Main.hs`.

```
data IntList = Nil | Cons(Int, Box IntList)
linear data Token = Token
def consume : Token → Int = λ(t:Token). case t of { Token → 1 }
```

**Accepted:**

| Program | Result |
|---|---|
| `let x = 2 in if x < 3 then x * 10 else 0` | `20` |
| `sum (map inc [1,2,3])` with recursive `map`, `sum` over `IntList` | `9` |
| `let t = Token in consume t` (free function, linear argument) | `1` |
| `let t = Token in let k = λ°(n:Int). consume t + n in k 41` | `42` |
| `linear data Pair = P(Token, Int)`; `case P(Token, 5) of { P(t, n) → consume t + n }` | `6` |

**Rejected:**

| Program | Error |
|---|---|
| `let t = Token in consume t + consume t` | `Duplicate` |
| `let t = Token in 1` | `Dropped` |
| `let t = Token in if true then consume t else 0` | `BranchMismatch` |
| `let t = Token in let k = λ(n:Int). consume t in k 1` | `LinearCapture` |
| `let t = Token in let k = λ°(n:Int). consume t in k 1 + k 2` | `Duplicate` |
| `data Bad = B(Token)` | `LinearField` |
| `data L = N \| C(Int, L)` | `InfiniteSize` |
| `case Nil of { Nil → 0 }` | `NonExhaustive` |
| `1 + true` | `Mismatch` |
