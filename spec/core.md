# Keel Core: specification

Keel Core is the small calculus that every part of Keel elaborates into: the surface language,
the REPL and the compiler. It is built in four stages, each extending the previous one:

| Stage | Calculus | Adds | Status |
|---|---|---|---|
| 1 | λK₁ | Linear types, functions, `data`, `case`, `Box` | done |
| 2 | λK₂ | Effects, tail-resumptive handlers, fixed-width checked arithmetic, `Panic`, `Diverge` | done |
| 3 | λK₃ | Second-class references `&` / `&mut`, `var`, assignment; elaborated to state passing | done |
| 4 | λK₄ | `codata`, rank-1 type and effect polymorphism, monomorphization | done |
| 5 | — | Bitwise operations, integer conversions, the `MMIO` effect (systems additions, §5) | done |

The executable reference checker and evaluator live in `ref/` (Haskell). Every rule below
corresponds to a case in `ref/src/Keel/Check.hs`, `Eval.hs`, `Elab.hs` or `Mono.hs`, and the examples in
each stage's examples section (§1.6, §2.7, §3.6, §4.6) are the tests in `ref/test/Main.hs`. The whole
pipeline (place rules → elaboration → checking → monomorphization → checking again) is
`compile` in `ref/src/Keel/Mono.hs`.

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

---

## 2. λK₂: effects

Stage 2 makes every side effect visible in types. Functions carry the effects their body
may perform, handlers discharge effects without a runtime, integers get fixed widths with
checked arithmetic, and recursion becomes the visible effect `Diverge`.

### 2.1 Syntax (additions and changes)

```
ι ::= i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64     integer types
ε ::= { l₁, …, lₙ }                                     effects: finite sets of labels
τ ::= Unit | Bool | ι | τ →ε τ | τ ⊸ε τ | D | Box τ     Int of §1 is now i64

e ::= …
    | () | n:ι                                          literals carry their type
    | e ⊕ e                                             ⊕ ∈ { +, -, * } checked, { +%, -%, *% } wrapping,
                                                        { +|, -|, *| } saturating, { ==, < }
    | op(e)                                             perform an operation
    | handle e with l { op₁ x → e₁ ; … ; opₙ x → eₙ }   tail-resumptive handler

decl ::= … | effect l { op₁ : τ ⇒ τ ; … }
```

`τ → σ` abbreviates `τ →{} σ`, so the stage 1 rules are the special case of empty effects.
Keel Core is explicitly typed: the surface language infers literal widths and inserts
annotations.

**Built-in labels:**

| Label | Operations | Handleable | Raised by |
|---|---|---|---|
| `IO` | `out : i64 ⇒ Unit` | yes | `out(e)`; at top level, appends to the program's output trace |
| `Panic` | none | no | checked arithmetic overflow |
| `Diverge` | none | no | referencing a definition from its own recursive group (§2.4) |

`Panic` is deliberately not handleable inside Keel Core: a panic ends the program, and the
reset handler of `notes.md` §16 lives in the runtime outside the calculus. A `+?` operator
returning `Option` waits for polymorphism (stage 4); stage 2 has no explicit `panic` term,
since it would need usage rules for "consumes any linear variables".

**Design note: effect sets now, rows later.** Koka-style row variables (`⟨l | ρ⟩`) only pay
off once functions can be polymorphic, which is stage 4. Until then effects are closed sets
with subsumption (§2.3), and stage 4 adds row variables on top.

### 2.2 Typing

The judgment gains an effect: `Γ ⊢ e : τ ! ε` means evaluating `e` may perform the operations
of `ε` and no others. Values (variables, literals, λ, constructors of values) have effect `{}`;
compound terms take the union of their parts. The algorithmic form is
`Γ ⊢ e ⇒ τ ! ε ▷ U`, with usage U exactly as in §1.3. The new and changed rules:

```
         Γ, x:τ ⊢ e : σ ! ε     Free(Γ)                  Γ, x:τ ⊢ e : σ ! ε
 (Lam) ─────────────────────────────────    (LLam) ──────────────────────────────
         Γ ⊢ λ(x:τ). e : τ →ε σ ! {}                   Γ ⊢ λ°(x:τ). e : τ ⊸ε σ ! {}

         Γ₁ ⊢ e₁ : τ ⇒ε σ ! ε₁    Γ₂ ⊢ e₂ : τ ! ε₂
 (App) ────────────────────────────────────────────────
         Γ₁ ⋈ Γ₂ ⊢ e₁ e₂ : σ ! ε₁ ∪ ε₂ ∪ ε

         Γ₁ ⊢ e₁ : ι ! ε₁    Γ₂ ⊢ e₂ : ι ! ε₂
 (Op)  ───────────────────────────────────────────    π = {Panic} for checked + - *, {} otherwise
         Γ₁ ⋈ Γ₂ ⊢ e₁ ⊕ e₂ : ι ! ε₁ ∪ ε₂ ∪ π         (result Bool for == <)

         (op : τ ⇒ σ) ∈ l      Γ ⊢ e : τ ! ε
 (Perform) ──────────────────────────────────
             Γ ⊢ op(e) : σ ! ε ∪ {l}

         Γ ⊢ e : τ ! ε     l = { opᵢ : τᵢ ⇒ σᵢ }     Free(Γ)     Γ, x:τᵢ ⊢ eᵢ : σᵢ ! εᵢ   (each opᵢ exactly once)
 (Handle) ────────────────────────────────────────────────────────────────────────────────────────────────
             Γ ⊢ handle e with l { op₁ x → e₁ ; … } : τ ! (ε ∖ {l}) ∪ ε₁ ∪ … ∪ εₙ

         Γ ⊢ e : τ ! ε     τ <: τ'     ε ⊆ ε'
 (Sub) ─────────────────────────────────────────
                  Γ ⊢ e : τ' ! ε'
```

In (Handle), `Free(Γ)` applies to the clauses only: a clause may run any number of times, so
like a free λ it can't capture linear variables (`LinearCapture`). The handled expression `e`
uses the context normally. The clauses' own effects `εᵢ` go to the *enclosing* handlers.

**Definitions and `main`.** A `def` body must have effect `{}`: definitions are evaluated
once at program start, and in practice they are λs. `main` may leave only the machine-provided
effects `{IO, Panic, Diverge}` unhandled; anything else is `Unhandled`.

**New errors:** `EffectMismatch` (the types agree except that an effect is missing from a
signature), `Unhandled`, `NonPositive` (§2.4). Handling an effect with a missing or repeated
operation is `NonExhaustive`; handling `Panic` or `Diverge` is `Unbound`.

### 2.3 Subtyping

```
 τ' <: τ    ε ⊆ ε'    σ <: σ'           τ' <: τ    ε ⊆ ε'    σ <: σ'
 ─────────────────────────────          ─────────────────────────────          τ <: σ
   τ →ε σ  <:  τ' →ε' σ'                  τ →ε σ  <:  τ' ⊸ε' σ'             ─────────────     τ <: τ
                                          (also ⊸ <: ⊸)                     Box τ <: Box σ
```

A function with fewer effects can be used where more are allowed: a pure function can be
passed to `map`, which accepts `i64 →{Panic} i64`. A free function can be used where a linear
one is expected, since calling it once is always allowed. This removes stage 1's limitation.
The checker applies subsumption wherever a type is checked against an expected one
(arguments, constructor fields, `def` signatures, handler clauses); `case` and `if` branches
must still have equal types.

### 2.4 Divergence and positivity

`Diverge` is the only way a Keel Core program can fail to terminate, which makes
"guaranteed to terminate" a property checked from effects (`notes.md` §13).

- **Recursive groups.** Build the reference graph of top-level definitions. The group of `f`
  is the set of definitions that reach `f` and are reached from it. While checking `f`, a
  *reference* (not just a call) to any member of its group has effect `{Diverge}`. Counting
  references rather than calls matters: in `def f = λk. twice f k`, `f` is passed as an
  argument and called by `twice`, and the reference still marks the loop.
- **Strict positivity (well-formedness rule 4).** A data type may not occur to the left of an
  arrow inside its own definition, following other data types transitively. Otherwise
  `data T = MkT(T → i64)` would allow self-application and a loop with no recursive definition.

Recursion is *marked*, not yet *checked*: a structurally recursive function such as `map`
still carries `Diverge`. A totality checker that removes `Diverge` from provably terminating
recursion is future work (`notes.md` §13).

### 2.5 Operational semantics

Evaluation now runs under a **handler stack** `H` (innermost first) and may produce an output
trace or a panic: `H; ρ ⊢ e ⇓ r` where `r` is a value or `panic`. All stage 1 rules carry `H`
unchanged, and a `panic` in any premise propagates. Closures run under the stack of their
*call*, not their creation (deep handlers).

```
               H' = (l, {opᵢ ↦ xᵢ.eᵢ}, ρ) · H      H'; ρ ⊢ e ⇓ v
 (Handle)  ─────────────────────────────────────────────────────────
               H; ρ ⊢ handle e with l { … } ⇓ v

            H; ρ ⊢ e ⇓ v     H = H₁ · (l, C, ρ_c) · H₂     op ∈ C, and no frame of H₁ handles op
            C(op) = x.e'     H₂; ρ_c, x ↦ v ⊢ e' ⇓ v'
 (Perform) ─────────────────────────────────────────────────────────────────────────────────────
            H; ρ ⊢ op(e) ⇓ v'

            H; ρ ⊢ e ⇓ n     no frame of H handles out
 (Out)     ─────────────────────────────────────────────    appends n to the output trace
            H; ρ ⊢ out(e) ⇓ ()
```

The clause runs under `H₂`, the handlers *outside* the one that caught the operation, so a
clause that performs the same operation reaches the next handler out instead of looping. The
clause's value *is* the operation's result: there is no continuation to capture, so a handler
compiles to an ordinary function call (dependency injection). This is what makes mocking
hardware free: the same driver code runs against a real `MMIO` handler in firmware and a mock
one in tests (§2.7).

**Arithmetic.** For `ι` with range `[lo, hi]` and exact result `r`:
- **checked:** `r` if it's in range, else `panic`;
- **wrapping:** `lo + (r − lo) mod (hi − lo + 1)` (two's complement);
- **saturating:** `r` clamped to `[lo, hi]`.

### 2.6 Metatheory

**Theorem 1 (type soundness, extended).** A well-typed `main` either evaluates to a value of
its type, panics, or diverges; it never gets stuck. Every operation it performs is handled by
an enclosing handler or is `out`.

**Theorem 4 (effect soundness).** If `Γ ⊢ e : τ ! ε` and evaluating `e` performs operation
`op` of label `l` while no handler inside `e` catches it, then `l ∈ ε`. If evaluation panics,
`Panic ∈ ε`.

*Sketch.* Induction on the evaluation derivation. (Perform) contributes `{l}`; (Handle) removes
`l` exactly when its frame catches every `op` of `l` performed by its body (it handles all of
them by exhaustiveness) and adds the clauses' effects, which run under the outer stack. A
closure's body effects are latent in its arrow type and are released by (App). Subsumption
only enlarges ε.

**Theorem 5 (termination).** If `⊢ program`, `· ⊢ main : τ ! ε` and `Diverge ∉ ε`, then
evaluation of `main` terminates (with a value or a panic).

*Sketch.* Without `Diverge`, every recursive definition the evaluation reaches was entered
only through references outside its own group, and a definition's body can't re-enter its
group without a `Diverge` reference, which would put `Diverge` into the effect of the call
that reaches it. What remains is simply typed λ-calculus with strictly positive data,
non-recursive `case`, and handlers whose clauses run under strictly smaller stacks. It
normalizes by a standard reducibility argument (Tait's method), with handler clauses
interpreted as functions of the outer stack.

**Theorem 2 (linearity), qualified.** Theorem 2 holds for executions that don't panic. A
panic ends the program with live linear values; that is the intended semantics, since the
reset handler restarts the system. Handler clauses never hold linear values (rule Handle), so
running a clause zero or many times can't duplicate or lose one.

### 2.7 Examples

```
data W = W(i64, i64)
effect MMIO { read : i64 ⇒ i64 ; write : W ⇒ Unit }

def send : IntList →{MMIO, Diverge} Unit = λ(xs:IntList). case xs of
  Nil → ()
  Cons(c, rest) → if read(4) == 1 then let done = write(W(0, c)) in send (unbox rest)
                  else send (Cons(c, rest))

main = handle send([72, 105]) with MMIO {        -- a mock UART
  read addr → 1 ;
  write w → case w of { W(reg, v) → out(v) }
}
```

**Accepted:**

| Program | Result |
|---|---|
| the mock UART above | `()`, output `[72, 105]` |
| `handle out(5) with IO { out x → out(x * 10) }` | `()`, output `[50]` (clause reaches the outer handler) |
| `250:u8 +% 10:u8` | `4:u8` |
| `100:i8 *% 2:i8` | `-56:i8` |
| `250:u8 +| 10:u8` | `255:u8` |
| `-100:i8 -| 100:i8` | `-128:i8` |
| `250:u8 + 10:u8` | panic |
| `let a = out(1) in 250:u8 + 10:u8` | panic, output `[1]` |
| `sum (map double [1,2,3])` with pure `double : i64 → i64` (subsumption) | `12` |
| `apply1 (λn. n +% 1)` where `apply1 : (i64 ⊸ i64) → i64` | `2` |

All stage 1 examples still hold. Their types now record effects: `inc : i64 →{Panic} i64` and
`map : (i64 →{Panic} i64) → IntList →{Panic, Diverge} IntList`.

**Rejected:**

| Program | Error |
|---|---|
| `main = read(4)` | `Unhandled` |
| `def bad : i64 → i64 = λn. n + 1` | `EffectMismatch` (Panic missing) |
| `def loop : i64 → i64 = λn. loop n` | `EffectMismatch` (Diverge missing) |
| `def f : i64 → i64 = λk. twice f k` | `EffectMismatch` (recursion through an argument) |
| `data T = MkT(T → i64)` | `NonPositive` |
| `let t = Token in handle out(1) with IO { out x → let r = consume t in () }` | `LinearCapture` |
| `handle read(4) with MMIO { read a → 1 }` | `NonExhaustive` |
| `handle 1 with Panic {}` | `Unbound` |
| `1:u8 + 1:i64` | `Mismatch` |
| `300:u8` | `Mismatch` |

---

## 3. λK₃: second-class references

Stage 3 adds the mutation style chosen in `notes.md` §16: `&` and `&mut` parameters, `var`
locals and assignment. None of it is new semantics. λK₃ is defined by **elaboration into
λK₂**: every reference becomes pure state passing, which is the claim "`&mut` is syntax
sugar over pure code" made precise and executable (`ref/src/Keel/Elab.hs`).

### 3.1 Syntax (additions)

```
π ::= τ | &τ | &mut τ                  parameter types
τ ::= … | τ ⊗ τ                         pair (added to the core; the elaboration needs it)
    | π →ε τ | π ⊸ε τ                   arrows take parameter types

e ::= …
    | (e, e) | let (x, y) = e in e      pairs (core)
    | λ(&x:τ). e | λ(&mut x:τ). e        reference parameters
    | e(&x) | e(&mut x)                 borrows: only as a function argument
    | var x = e in e                    mutable local
    | x := e                            assignment, of type Unit
    | e; e                              sequencing (first part has type Unit)
```

A **place** is a `&`/`&mut` parameter or a `var`. `&mut` parameters and `var`s are mutable;
`&` parameters are read-only. Reading a place `x` reads its current value (a copy for `Free`
types, a move for `Lin` types).

`τ ⊗ σ` has kind `Lin` if either component does. Its typing rules are the standard tensor
rules (both components used in disjoint contexts; `let (x, y)` binds both, linear ones must
be used). For sizes and positivity it behaves like a data type with two fields.

### 3.2 Place rules

These rules are what make references *second-class*. They are checked on the λK₃ program
before elaboration (`checkRefs`):

1. **References stay in parameters** (`RefEscape`). `&τ` and `&mut τ` appear only as the
   parameter type of an arrow: never as a result, a data field, an operation type or inside
   a pair. `&x` and `&mut x` appear only as a function argument.
2. **Assignment needs a mutable place.** `x := e` and `f(&mut x)` require `x` to be a `&mut`
   parameter or `var` (`NotAPlace` if `x` isn't a place, `NotMutable` if it's a `&` parameter).
   `f(&x)` requires a place of either kind.
3. **No capture** (`PlaceCapture`). A λ, λ° or handler clause can't mention any place from
   outside it. Its only places are its own reference parameter and the `var`s inside it.
4. **Handled expressions only read outer places** (`PlaceCapture`). Inside
   `handle e with …`, `e` may read places from outside but not assign or borrow them, because
   a handler could otherwise observe them mid-update.

**Exclusivity holds by construction.** Every λ has one parameter, and a closure can't
capture places (rule 3), so a function with a reference parameter must be applied to exactly
one borrow, and nothing else in scope can reach that place during the call. Two `&mut` to the
same variable in one call, or reading a place while a call mutates it, can't be written.
Once functions take several parameters, this becomes an explicit rule (Hylo's law of
exclusivity).

### 3.3 Elaboration to λK₂

Types:

```
⟦&τ →ε σ⟧ = ⟦&mut τ →ε σ⟧ = ⟦τ⟧ →ε ⟦σ⟧ ⊗ ⟦τ⟧        (same for ⊸)
```

A function with a reference parameter returns its result *and* the final value of the
parameter. `&` is elaborated like `&mut` (pass and return); the place rules forbid assigning
it, so the returned value is the one passed in, and a later optimization can drop the copy.

Terms are translated left to right, call-by-value, threading the **current name** of each
place. Each assignment and each borrowing call introduces a fresh name (`x#n`) for the new
version:

| λK₃ | λK₂ |
|---|---|
| `x := e; rest` | `let x#1 = e in rest[x ↦ x#1]` |
| `var x = e in body` | `let x#1 = e in body[x ↦ x#1]` |
| `f(&mut x); rest` | `let (r, x#2) = f x#1 in rest[x ↦ x#2]` (r is the call's value) |
| `λ(&mut x:τ). body` | `λ(x:τ). body'`, where `body'` ends in `(v, x#n)`: the value and the final version of x |
| `e₁; e₂` | `let _ = e₁ in e₂` |

Subterms that use no references are copied unchanged (with place reads renamed). When a
later sibling needs elaboration, earlier values are let-bound first, so evaluation order is
preserved. `if`/`case` branches each receive a copy of the rest of the computation. That is
correct but can grow exponentially for nested mutating branches; join points fix it when it
matters.

Example (output of `elaborate`, names as generated):

```
linear data Counter = Counter(i64)
def tick : &mut Counter → Unit = λ(&mut c:Counter). case c of Counter(n) → c := Counter(n +% 1)
main = var k = Counter(0) in tick(&mut k); case k of Counter(v) → v
```

becomes

```
def tick : Counter → Unit ⊗ Counter =
  λ(c:Counter). case c of Counter(n) → let c#0 = Counter(n +% 1) in ((), c#0)
main = let k#1 = Counter(0) in
       let (r#2, k#3) = tick k#1 in
       let seq#4 = r#2 in
       case k#3 of Counter(v) → v
```

The elaborated program is then checked by the λK₂ checker (`checkSurface` = place rules,
then elaborate, then `checkProgram`). Linearity of places is therefore enforced *on the
elaboration*: a `var` holding a linear value must be moved out before its scope ends
(`Dropped`), and moving it twice is `Duplicate`.

### 3.4 Semantics

The meaning of a λK₃ program is the meaning of its elaboration. There is no new evaluation
rule.

### 3.5 Metatheory

**Theorem 6 (elaboration preserves typing).** If a λK₃ program satisfies the place rules and
its elaboration is well typed in λK₂, all the λK₂ theorems apply to it. Moreover, if `e` is
well typed in λK₃'s natural typing (places typed by their contents, `x := e` : Unit), then
`⟦e⟧` is well typed in λK₂ with the translated types.

*Sketch.* Induction on `e`, carrying the map from places to current names. Each translation
row produces a λK₂ term whose type matches by the type translation above. Fresh names never
clash (they contain `#`). Linear places are threaded: each version is bound once and consumed
by the next assignment, borrow or final read. The reference implementation checks the
elaborated program anyway, so this theorem is checked on every program, not just trusted.

**Theorem 7 (state passing agrees with mutation).** Give λK₃ a direct semantics with a store,
where places are mutable cells, borrowing passes a cell, and assignment updates it in place.
For programs satisfying the place rules, evaluating `e` in this store semantics and evaluating
`⟦e⟧` in λK₂ produce the same result and the same output trace.

*Sketch.* Simulation relation: a store `S` is related to the λK₂ environment that binds each
place's current name to `S(place)`. Assignment updates the cell / binds the next version; a
borrowing call passes the cell / passes the value and rebinds the returned version. The place
rules ensure no other path to the cell exists during the call (no capture, one borrow per call,
handlers can't touch outer places), so the callee's final cell content equals the value it
returns. This is the formal content of "mutable value semantics": with second-class references,
in-place mutation is *unobservable* compared to pure state passing. That is why the compiler is
free to implement `&mut` as a pointer and update memory in place.

### 3.6 Examples

**Accepted:**

| Program | Result |
|---|---|
| `var c = 0 in bump(&mut c); bump(&mut c); c * 10` with `bump(&mut n) = n := n + 1` | `20` |
| `var k = Counter(0) in tick(&mut k); tick(&mut k); case k of Counter(v) → v` (linear) | `2` |
| `drain(&mut buf)` over `[72, 105]` under the mock UART (below), then `buf` | `Nil`, output `[72, 105]` |
| the same written by hand: `drainSP : IntList → Unit ⊗ IntList` | `Nil`, output `[72, 105]` |
| `var l = [5,6,7] in len(&l)` with a `&` parameter | `3` |
| `var t = Token in consume t` | `1` |

```
def drain : &mut IntList →{MMIO, Diverge} Unit = λ(&mut q:IntList). case q of
  Nil → ()
  Cons(c, rest) → write(W(0, c)); q := unbox rest; drain(&mut q)
```

The `drain` / `drainSP` pair is the executable form of Theorem 7: the version with `&mut` and
the hand-written state-passing version produce the same value and the same output.

**Rejected:**

| Program | Error |
|---|---|
| `def f : i64 → &mut i64 = …` | `RefEscape` |
| `data D = D(&i64)` | `RefEscape` |
| `var x = 1 in let y = &mut x in 0` | `RefEscape` |
| `var x = 1 in let g = λ(u:Unit). x in g ()` | `PlaceCapture` |
| `λ(&x:i64). x := 1` | `NotMutable` |
| `let y = 1 in y := 2` | `NotAPlace` |
| `let y = 1 in bump(&mut y)` | `NotAPlace` |
| `var t = Token in 1` | `Dropped` |
| `var t = Token in let a = consume t in consume t` | `Duplicate` |
| `var x = 0 in handle (x := 1) with IO { … }` | `PlaceCapture` |
| `var x = 0 in handle out(1) with IO { out v → out(x) }` | `PlaceCapture` |

### 3.7 Limitations and open questions

- **One parameter per function.** A function can borrow only one place. `swap(&mut a, &mut b)`
  needs n-ary functions in the core, and with them an explicit exclusivity rule (§3.2).
- **`&` on linear values is weak.** `&` is pass-and-return, and reading a linear place moves
  it, so a function can only pass a `&Lin` value along, not inspect it. Non-consuming reads
  (for example, reading `Free` fields of a linear value) are future work.
- **Places are whole variables.** There are no field paths (`r.tail := …`); update a field by
  rebuilding the value. Field paths are sugar to add later.
- **Stateful handlers are not covered.** A handler clause can't capture places (rule 3), so a
  mock device can't keep its own state yet. Handler-owned state (Koka's handler-local `var`)
  needs either a primitive with its own semantics or a state-passing translation of every
  operation the handled code performs; this is an open design question.

---

## 4. λK₄: codata and polymorphism

Stage 4 adds the last two pieces of `notes.md` §16: **codata as the interface mechanism**
and **explicit dictionaries + monomorphization** in place of type classes. Polymorphism is
rank-1 only, so every program can be specialized to a monomorphic one before code
generation, which is how the compiler will run it.

### 4.1 Syntax (additions)

```
α, β                                     type variables
ρ                                        effect variables (written 'e in the reference implementation)
ε ::= { l₁, …, lₙ, ρ₁, …, ρₘ }            effects may contain effect variables

τ ::= … | α | D[τ₁, …, τₙ]                 data and codata types take type arguments
σ ::= ∀(α₁:κ₁) … (αₙ:κₙ) ρ₁ … ρₘ. τ        type schemes: only as the type of a top-level def

e ::= …
    | C[τ̄](e₁, …, eₙ)                      constructors name their type arguments
    | f[τ̄; ε̄]                              instantiate a polymorphic definition
    | cocase D[τ̄] { o₁ → e₁ ; … ; oₙ → eₙ } build a codata value
    | e.o                                   observe it
    | e₁ +? e₂  (also -?, *?)               arithmetic returning Option ι instead of panicking

decl ::= [linear] data D α₁ … αₙ = C₁(τ, …) | …
       | codata D α₁ … αₙ { o₁ : τ ; … }
       | def f : σ = e
```

Keel Core stays explicitly typed: every instantiation, constructor and cocase names its type
arguments. The surface language infers them. Built in: `data Option a = None | Some(a)`.

**Design note: why codata.** A codata type is defined by its *observations*, not its
constructors. A `cocase` is a record of operations that closes over its environment, which
is what an interface implementation, a driver vtable or a type-class dictionary is. One
mechanism covers all three:

```
codata Serial { send : i64 →{IO} Unit }                     an interface
codata Ord a  { lt : a → a → Bool }                         a dictionary

def sort : ∀(a:Free). Ord a → List a →{Diverge} List a = …  explicit dictionary passing
main = sort[i64] ordI64 [3, 1, 2]
```

There is no instance resolution: the dictionary is an ordinary argument. After
monomorphization the dictionary is a known constant, so inlining (milestone M4) turns `o.lt x y`
into `x < y`. None of the type-class problems listed in the video (coherence, orphan
instances, global uniqueness) can arise.

### 4.2 Kinds and typing

**Kinds with type variables.** Each quantified variable declares a kind. `(α:Free)` may be
copied and dropped and can only be instantiated with `Free` types (`KindMismatch`
otherwise). `(α:Lin)` may be instantiated with anything, so the body must use an `α` value
exactly once. Linear is the safe default: `∀(a:Lin). a → a ⊗ a` is rejected (`Duplicate`).

```
κ(α)      = the declared kind of α
κ(D[τ̄])   = Lin   if D is `linear data`, or some τᵢ has kind Lin
          = Free  otherwise (and always for codata)
```

So `List[i64]` is `Free` and `List[Token]` is `Lin`, from a single declaration. Inside a
declaration its parameters count as `Free` for rule 1 (§1.2): the linearity of an argument
moves to the whole type instead of making the declaration ill-formed.

**Rules.** Let `θ = [τ̄/ᾱ, ε̄/ρ̄]` be a substitution.

```
            def f : ∀(ᾱ:κ̄) ρ̄. τ ∈ Σ     κ(τᵢ) ⊑ κᵢ  (Lin types only for Lin variables)
 (Inst)  ──────────────────────────────────────────────────────────────────────────────    Diverge if f is in
            Γ ⊢ f[τ̄; ε̄] : θτ ! {}                                                          the current group

            C : (σ̄) → D ᾱ      Γᵢ ⊢ eᵢ : [τ̄/ᾱ]σᵢ
 (Con)   ──────────────────────────────────────────          (Case) substitutes the scrutinee's
            ⋈Γᵢ ⊢ C[τ̄](ē) : D[τ̄]                              arguments into the pattern types

            codata D ᾱ { oᵢ : σᵢ }      Free(Γ)      Γ ⊢ eᵢ : [τ̄/ᾱ]σᵢ ! {}   (each oᵢ exactly once)
 (Cocase) ───────────────────────────────────────────────────────────────────────────────────
            Γ ⊢ cocase D[τ̄] { o₁ → e₁ ; … } : D[τ̄] ! {}

            Γ ⊢ e : D[τ̄] ! ε      codata D ᾱ { …; o : σ; … }
 (Proj)   ──────────────────────────────────────────────────
            Γ ⊢ e.o : [τ̄/ᾱ]σ ! ε
```

A cocase can be observed any number of times, so like a free λ it can't capture linear
values (`LinearCapture`), and that is why codata is always `Free`. Its branches must be
effect-free (`EffectMismatch`): a branch is a value such as a λ, and the effects go inside it.

A polymorphic definition is checked once, with its type variables **rigid** (equal only to
themselves) and its effect variables treated as opaque labels. Effect polymorphism therefore
needs no new machinery: `pmap : ∀a b ρ. (a →ρ b) → List a →{ρ, Diverge} List b` checks
because `f x` has effect `{ρ}`, and `pmap[i64; i64; {Panic}]` substitutes `ρ ↦ {Panic}`.

**Rank-1 only** (`HigherRank`). `∀` appears only at the top of a `def`'s type, never inside a
type. Using a polymorphic definition without instantiating it is a `Mismatch`. This rules out
runtime type passing, which monomorphization needs. A polymorphic function argument is an
explicit codata value instead.

### 4.3 Well-formedness with parameters

- **Variance.** For each data and codata type, compute the polarities at which each
  parameter occurs (positive, negative or both), as the least fixpoint over all declarations.
  `codata Ord a { lt : a → a → Bool }` has `a` negative. `List a` has `a` positive.
- **Positivity through parameters (rule 4).** When checking that `D` occurs only positively
  in its own definition, an occurrence inside `E[…, τ, …]` takes the polarity of `E`'s
  parameter. So `data T = T(Box (Neg T))` with `data Neg a = Neg(a → i64)` is `NonPositive`,
  and so is `codata Bad { f : Bad → i64 }`, which would allow a loop with no recursion.
- **Finite size (rule 2), conservatively.** Type arguments count as stored inline, so
  `data L = C(i64, Wrap L)` with `data Wrap a = W(a)` is `InfiniteSize`. This also rejects
  some finite types whose parameter only sits behind `Box` or a function; precise per-parameter
  layout analysis is future work.

### 4.4 Monomorphization

`Mono.hs` is the worklist of `notes.md` §4:

1. Start from `main` and every monomorphic definition, and collect each instantiation
   `f[τ̄; ε̄]`. All of these are closed.
2. For each new instance, substitute into `f`'s body and type, name it `f[τ̄; ε̄]`, and add the
   instantiations in the new body to the worklist.
3. Replace every `f[τ̄; ε̄]` with a reference to its instance, and drop the polymorphic
   definitions.

**Polymorphic recursion is rejected** (`PolyRecursion`). Inside a recursive group, members
may only be instantiated at the caller's own type variables. For example,
`depth : ∀a. Nested a → i64` calling `depth[List a]` is rejected; `pmap` calling
`pmap[a, b]` is fine. Effect arguments are unrestricted.

**Output.** No `∀`, no instantiation, and no type variable in any definition or in `main`
(`isClosed`). Data and codata declarations stay parameterized: they are layout *templates*,
and the backend lays out `List[i64]` and `List[Token]` separately, as Rust does with
generic structs. The output is checked again by the core checker (`compile`).

### 4.5 Semantics

Types are erased: `f[τ̄; ε̄]` evaluates like `f`, and `C[τ̄](ē)` like `C(ē)`. A `cocase` evaluates
to a codata value `⟨ρ, {oᵢ ↦ eᵢ}⟩` (its environment and branches). An observation runs the
branch in that environment, every time:

```
 H; ρ ⊢ e ⇓ ⟨ρ', {…, o ↦ e_o, …}⟩     H; ρ' ⊢ e_o ⇓ v
 ───────────────────────────────────────────────────────
                 H; ρ ⊢ e.o ⇓ v
```

Re-running a branch is safe: branches are effect-free and capture no linear values. `+?`
returns `Some(r)` when the exact result `r` is in range and `None` otherwise.

### 4.6 Examples

**Accepted** (each also monomorphized, checked as closed, and re-run: same result):

| Program | Result |
|---|---|
| `psum (pmap[i64; i64; {Panic}] inc [1,2,3])`, effect-polymorphic `pmap` | `9` |
| `psum (pmap[Token; i64; {}] consume [Token, Token])` (a list of linear tokens) | `2` |
| `greet loud; greet quiet; greet loud`, where `greet s = s.send 72; s.send 105` | `()`, output `[72, 105, 72, 105]` |
| `sort[i64] ordI64 [3,1,2]` with `ordI64 = cocase Ord[i64] { lt → λp q. p < q }` | `[1, 2, 3]` |
| `sort[i64] ordDesc [3,1,2]` with the reversed dictionary | `[3, 2, 1]` |
| `dup[i64] 3` with `dup : ∀(a:Free). a → a ⊗ a` | `(3, 3)` |
| `1 +? 2` / `250:u8 +? 10:u8` | `Some(3)` / `None` |

**Rejected:**

| Program | Error |
|---|---|
| `depth : ∀a. Nested a → i64` calling `depth[List a]` | `PolyRecursion` |
| `insert[Token]` where `insert : ∀(a:Free). …` | `KindMismatch` |
| `let g = pmap in 0` (no type arguments) | `Mismatch` |
| `def hr : (∀a. a → a) → i64` | `HigherRank` |
| `def dup : ∀(a:Lin). a → a ⊗ a = λx. (x, x)` | `Duplicate` |
| a `cocase` branch that uses a linear `Token` from outside | `LinearCapture` |
| `cocase Ord[i64] {}` | `NonExhaustive` |
| `codata Bad { f : Bad → i64 }` | `NonPositive` |
| `data T = T(Box (Neg T))`, `data Neg a = Neg(a → i64)` | `NonPositive` |
| `data L2 = C2(i64, Wrap L2)`, `data Wrap a = W(a)` | `InfiniteSize` |
| `def g : i64 →{'q} i64` with `'q` not bound | `Unbound` |

### 4.7 Metatheory

**Lemma (substitution).** If `def f : ∀(ᾱ:κ̄) ρ̄. τ = e` is well typed, the arguments
respect the declared kinds, and `θ = [τ̄/ᾱ, ε̄/ρ̄]` is closed, then `· ⊢ θe : θτ ! {}`. Kinds are
preserved because `κ(θτ)` can only become `Lin` where τ mentions an `α:Lin`, which the body
already treated linearly. Effects are preserved because subset and union commute with
substituting sets for labels.

**Theorem 8 (monomorphization terminates).** Under the polymorphic-recursion restriction,
the worklist reaches a fixpoint.

*Sketch.* Order recursive groups topologically. Inside a group, instances are created only
at the caller's own type arguments, so a group entered at closed arguments `τ̄` creates
instances whose arguments are drawn from `τ̄`: finitely many. Effect arguments range over
subsets of the finitely many labels in the program. Calls between groups go down the
topological order. Each step therefore creates finitely many instances.

**Theorem 9 (monomorphization preserves typing and meaning).** If `compile` accepts a
program, the monomorphic output is well typed, closed, and evaluates to the same outcome and
output trace as the original.

*Sketch.* Typing: by the substitution lemma, each instance is well typed at its closed
type, and replacing `f[τ̄; ε̄]` by the instance name preserves types. Meaning: evaluation
erases types, so an instance's body evaluates exactly like the polymorphic body. The test
suite checks the "same outcome" part on every accepted program.

**Theorem 1, 2, 4, 5 extend unchanged.** Codata adds a value form whose observation is a
closure call. The (Cocase) rule gives it the same guarantees as a free λ: no linear capture,
and effects only through the function types it returns.

### 4.8 Limitations

- **Data and codata parameters are types only.** A codata type can't be effect-polymorphic
  (`codata Stream ρ a`), so an interface fixes its effects (`Serial`'s `send` is `{IO}`).
- **No `Self` in codata.** The `notes.md` §16 sketch has `send : &mut Self → …`. That needs
  observations with a reference to the value itself; for now a codata value holds its state
  in its closure.
- **Observations re-run their branch.** This is cheap and correct because branches are
  effect-free values. A compiler would build the record of closures once.
- **The size rule is conservative over type arguments** (§4.3).
- **Instance names are strings** (`pmap[i64; i64; {Panic}]`). A compiler would intern them.

---

## 5. Additions for systems code (M3)

Three small extensions, added with the native back ends. None changes the metatheory: they are
new primitives with ordinary typing rules.

**Bitwise operations.** `e₁ ⊙ e₂` with `⊙ ∈ { land, lor, lxor, lsl, lsr }`: both operands have
the same integer type ι, the result has type ι, and the effect is `{}` (they can't overflow).
`lsl` wraps to the width. `lsr` is logical on unsigned types and arithmetic on signed ones. A
shift amount below 0 counts as 0, and 64 or more shifts everything out.

```
         Γ₁ ⊢ e₁ : ι ! ε₁    Γ₂ ⊢ e₂ : ι ! ε₂
 (Bits) ───────────────────────────────────────
         Γ₁ ⋈ Γ₂ ⊢ e₁ ⊙ e₂ : ι ! ε₁ ∪ ε₂
```

**Conversions.** `e as ι'` converts between integer types by wrapping (two's complement
truncation or extension, like Rust's `as`): if `Γ ⊢ e : ι ! ε` then `Γ ⊢ e as ι' : ι' ! ε`, and
the value is `lo + (n − lo) mod (hi − lo + 1)` for the range `[lo, hi]` of ι'.

**MMIO.** A built-in effect label with four operations:

| Operation | Type |
|---|---|
| `read8`, `read32` | `u64 ⇒ u8`, `u64 ⇒ u32` |
| `write8`, `write32` | `u64 ⊗ u8 ⇒ Unit`, `u64 ⊗ u32 ⇒ Unit` |

`main` may leave `MMIO` unhandled, like `IO`: the machine then performs the operations on device
memory. In the reference evaluator, which has no device memory, an unhandled MMIO operation
panics; a handler is how drivers are tested there. The operations are ordinary operations in
every other respect, so Theorem 4 (effect soundness) covers them: code whose type has no `MMIO`
never touches device memory.

The surface language adds `bitdata` register layouts on top of these (`spec/surface.md`); they
are elaborated away before Keel Core.
