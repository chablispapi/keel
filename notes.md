# Keel: a functional language that compiles to native code with no heavy runtime

Source: "The wasted potential of Haskell: language and compiler" (transcript in `transcription.txt`).

**Name: Keel.** The keel is the structural spine at the bottom of a ship: invisible, underneath
everything, keeping it stable. That fits a language for kernels and firmware. File extension
`.kl`, compiler `keelc`. (Before publishing, check the name isn't already taken on GitHub,
package registries or trademarks.)

## 1. Context

**The video's claim:** functional languages should be the best tool for low-level code (kernels,
drivers, memory manipulation), where type safety helps most. What makes Haskell slow is not
functional programming itself. It is a set of choices GHC committed to:

- lazy evaluation everywhere, which forces thunks and graph reduction
- type classes, which pass function dictionaries at runtime
- a GC that can't be turned off

The video also argues that compiling a fully applied lambda-calculus call is just `call`/`ret`.
The harder parts are partial application and higher-order functions.

**Our question:** no well-known functional language compiles straight to assembly without a heavy
runtime. What would such a language look like?

## 2. Prior art (the premise is only partly true)

| Language | Backend | Memory | Notes |
|---|---|---|---|
| Rust | LLVM | ownership / affine types | Effectively an ML-family language with C syntax, no GC |
| Roc | LLVM + its own dev backend | refcounting, in-place reuse | Pure and strict, no GC |
| Koka | C | Perceus refcounting | Functional code that updates data in place when it's safe |
| Lean 4 | C | refcounting ("Counting Immutable Beans") | Dependently typed, produces fast binaries |
| MLton | native | GC | Whole-program compiler; defunctionalizes all closures |
| MLKit | native | region inference | Standard ML with no GC required |
| Cogent | C | linear types | Used to write verified file systems for seL4 |
| ATS | C | linear types + dependent types | Close to C speed, with proofs |
| Pre-Scheme | C | manual | A Scheme subset with no GC |

Compiling through C or LLVM is just using a portable assembler. What matters is whether the
**execution model needs a runtime**, not which backend the compiler targets.

## 3. Design sketch

1. **Strict evaluation (call-by-value).** A known, fully applied call is `call`/`ret`. Laziness is opt-in: a `Lazy a` type, or codata for streams.
2. **Monomorphization instead of runtime dictionaries.** Ad hoc polymorphism is resolved statically, through explicit modules (ML functors or OCaml's modular implicits).
3. **Closures, the hard part:**
   - defunctionalization (MLton): each lambda becomes a constructor, and calling it becomes a `switch`
   - Rust-style closures: each closure is its own unboxed struct type, stored on the stack and inlined; boxing is explicit
   - eval/apply plus arity analysis ("Making a fast curry", Marlow & Peyton Jones) for unknown partial applications
4. **Memory without a GC:** linear/affine types by default, with refcounting plus reuse (Perceus) as an escape hatch for sharing, and regions or arenas.
5. **Data layout control:** values unboxed by default, explicit `Box`, and bit-level layouts (`bitdata`, an idea from the Habit language).
6. **Effects in the types** for MMIO, interrupts, and inline asm, so purity guarantees hold around them.
7. **Guaranteed tail calls and join points** ("Compiling without Continuations", 2017), so recursion becomes loops and jumps.

```haskell
-- strict, monomorphized, no GC. `-o` = linear arrow (argument consumed)
type List a = Nil | Cons a (Box (List a))

map : (a -> b) -> List a -o List b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)   -- input cell reused in place: zero allocation

-- hardware register layout, checked by the type system
bitdata Status = { tx_ready : 1, rx_ready : 1, _ : 6 }

device Uart at 0x4000_1000 {
  data   : Reg u8     W @ 0x00
  status : Reg Status R @ 0x04
}

putc : &Uart -> u8 -> () ! MMIO
putc u c = do
  waitUntil (read u.status).tx_ready   -- tail-recursive → loop
  write u.data c
```

**Compiler pipeline:** parse → typecheck (Hindley–Milner, or bidirectional checking with
quantitative/linear types) → monomorphize → closure conversion / defunctionalization → ANF IR
with join points → insert linearity checks and refcounts, plus reuse analysis → SSA → register
allocation → asm.

**Why such languages are rare:**

- A GC makes many things easy: sharing persistent data structures, uniform value representation, separate compilation, and closures that escape their scope. Without one, that complexity moves into the type system (Rust's borrow checker is that cost).
- Monomorphization makes compiles slow.
- Writing a native backend is expensive, so almost everyone targets C or LLVM.

**The unexplored space:** Rust's memory model combined with Koka or Lean's purity and in-place
reuse. Roc and Koka are the closest attempts.

## 4. Deep dive: monomorphization

The problem: for `id : a -> a`, the compiler doesn't know the size of `a` or which register holds it.

| | Uniform representation | Monomorphization |
|---|---|---|
| Idea | Every value is one machine word | Make a separate copy of the function per type |
| Used by | Haskell, OCaml, Java (type erasure) | Rust, C++, MLton, Zig, Swift (when optimizing) |
| Cost | Boxing, allocation, pointer chasing, tag bits, dictionaries | Larger code, slower compiles |
| Separate compilation | Easy | Function bodies must cross module boundaries |

With monomorphization, dictionary passing costs nothing at runtime: each dictionary becomes a
known constant record, so a method call inlines to the right instruction (`dict.plus` → `add`).
The video's other objections to type classes are about the type system (coherence, principal
types), not runtime cost.

The algorithm runs after type checking, on a core IR where every call has explicit type arguments:

```python
# ponytail: sketch, not production
def monomorphize(program, entry="main"):
    out, seen = {}, set()
    work = [(entry, ())]                      # (function name, concrete type args)
    while work:
        name, tys = work.pop()
        if (name, tys) in seen: continue
        seen.add((name, tys))
        fn = program[name]
        body = substitute(fn.body, dict(zip(fn.tyvars, tys)))   # a := Int everywhere
        for callee, args in calls_in(body):   # each call now has concrete types
            work.append((callee, args))
        out[mangle(name, tys)] = rewrite_calls(body, mangle)    # map@Int@Bool
    return out
```

Example: `map isEven [1,2,3]` and `map show [True]` produce `map_Int_Bool` and `map_Bool_String`.

**Interaction with closures:** in Rust, each lambda has a unique type, so `map` is specialized per
closure and the call to `f` inside it is a known call that gets inlined: a tight loop with no
function pointer. MLton monomorphizes the whole program and then defunctionalizes, so every
remaining higher-order call becomes a `switch`.

**Where it breaks:**

1. **Polymorphic recursion.** `data Nested a = Flat a | Nest (Nested (List a))` needs infinitely many copies, so the worklist never ends. Reject it, or require explicit boxing.
2. **Higher-rank types and existentials.** The type is chosen at runtime, so the code needs an explicit vtable (`dyn Trait`).
3. **Separate compilation.** Libraries must ship generic function bodies (Rust stores MIR in `.rlib` files; C++ uses headers). The linker removes duplicate copies (COMDAT folding).
4. **Code bloat and compile time.**

**The middle ground is to specialize by memory layout, not by type.** Machine code only depends
on size, alignment, and how to copy and destroy a value.

- **Go** (GC-shape stenciling): one copy per memory shape, plus a small dictionary for the rest.
- **Swift**: compiles generic code once using value witness tables, and specializes only as an optimization. That gives it ABI-stable generics.
- **Rust's "polymorphization"**: an experimental pass that merges copies which don't depend on the type parameter.

**Choice for our language:**

- Monomorphize by default.
- Merge copies that have the same memory layout.
- Make dynamic dispatch (`dyn`) explicit.
- Reject polymorphic recursion unless the recursive part is explicitly boxed.
- Ship the typed IR in libraries.
- Erase types after type checking (QTT's 0-multiplicity marks what is erased).

## 5. Deep dive: lambda calculus → assembly

```
t ::= x | λx. t | t t        -- one rule, β: (λx. body) arg → body[x := arg]
```

**When arguments are evaluated (reduction strategy):**

| Strategy | Rule | Used by |
|---|---|---|
| Call-by-value | Evaluate the argument, then call | ML, Rust, Scheme |
| Call-by-name | Pass the unevaluated argument; recompute at every use | Algol-60 |
| Call-by-need | Like call-by-name, but cache the result after first use | Haskell |

Call-by-need needs a mutable thunk (an object that gets overwritten with its value) for every
argument. That makes the program a shared graph, which needs a GC, and adds an "already
evaluated?" check on every read. This is the source of the video's complaints. Call-by-value has
none of it: the argument is already a value in a register.

**How far evaluation goes:** compilers stop at weak head normal form. They never reduce inside a
lambda until it's called, which is what makes lambda calculus map onto hardware. Full
normalization (reducing inside function bodies too) is needed only by type checkers and
optimal-reduction projects (HVM, Lamping's algorithm).

**No literal substitution:** real implementations keep an environment of variable values and look
variables up in it (Landin, 1964). A function value is a **closure**: a pointer to the code plus
its environment. In context, the GHC book quote in the video is describing why naive substitution
is slow, which is the problem environments solve.

```python
# terms: ("var", i) de Bruijn index | ("lam", body) | ("app", f, a) | ("lit", n) | ("add", a, b)
def ev(t, env=()):
    match t:
        case ("var", i):    return env[i]                     # lookup, no substitution
        case ("lam", body): return ("clo", body, env)          # closure = code + env
        case ("app", f, a):
            _, body, cenv = ev(f, env)
            return ev(body, (ev(a, env),) + cenv)              # CBV: arg first, then "call"
        case ("lit", n):    return n
        case ("add", a, b): return ev(a, env) + ev(b, env)

add = ("lam", ("lam", ("add", ("var", 1), ("var", 0))))       # λx. λy. x + y
inc = ("app", add, ("lit", 1))                                 # partial application
assert ev(("app", inc, ("lit", 41))) == 42
assert ev(inc)[0] == "clo"                                     # add 1 is a closure holding x=1
```

De Bruijn indices replace variable names with positions, the same way stack offsets work.

**Three passes from λ to assembly**, on `let add = λx y. x + y in let inc = add 1 in inc 41`:

1. **ANF (A-normal form):** name every intermediate result: `let inc = add 1 in let r = inc 41 in r`.
2. **Closure conversion:** a lambda that uses outer variables becomes `{code_ptr, captured vars}`, and its code takes the environment as an explicit parameter.
   ```c
   int add_y(Env *e, int y) { return e->x + y; }       // inner λy, x comes from env
   Clo *add(int x) { return mk_clo(add_y, x); }        // returns {add_y, x}
   ```
3. **Hoisting (lambda lifting):** move all code to the top level. The program is now first-order, which is what assembly expresses.

```asm
; known, fully applied call (the video's "free" case)
    mov  edi, 3
    mov  esi, 4
    call add            ; plain call/ret, args in registers

; unknown function value: rdi = closure pointer, rsi = argument
    call [rdi]          ; jump to the code pointer stored in the closure, env = rdi
```

The real cost is not the call. It is **where the closure's environment lives and when it's
freed**: on the stack if it doesn't escape, on the heap if it does. Monomorphization and
defunctionalization remove most unknown calls, and linearity or refcounting decides when
environments are freed.

**Abstract machines:**

| Machine | Strategy | Notes |
|---|---|---|
| SECD (Landin, 1964) | CBV | The first; uses environments |
| CEK (Felleisen) | CBV | The evaluator above is essentially CEK |
| ZINC (Leroy) | CBV, multi-argument | OCaml's basis |
| Krivine | Call-by-name | Minimal |
| G-machine → STG (GHC) | Call-by-need | Graph reduction, the model the video criticizes |

**Choice for our language:** call-by-value plus weak head normal form, compiled through ANF,
closure conversion, and hoisting. Known calls become `call`; unknown calls go through closures.

## 6. Graph reduction hardware vs. compiling to a CPU

Dedicated graph reduction machines were built: SKIM (~1980), ALICE and GRIP (1980s), the
Reduceron (an FPGA design, ~2008–2012), and today HVM/Bend on GPUs. The 1980s machines lost for
the same reason Lisp machines did: ordinary CPUs got faster every year, and compilers (the
G-machine, then STG) learned to turn graph reduction into ordinary machine code.

- A graph reducer is the natural hardware for **call-by-need**: building nodes, "already evaluated?" checks, overwriting thunks with results, following pointers, parallel reduction.
- For **call-by-value plus weak head normal form**, a CPU is already the natural hardware: a known call is `call`/`ret`, arguments are registers, the environment is a stack frame, a closure is `call [rdi]`, and a tail call is `jmp`.
- A graph reducer is essentially an interpreter in hardware. Our compiler decides in advance which function each call goes to, each value's layout, whether a value is evaluated (under CBV it always is), and when memory is freed. That work disappears from the running program.
- Graph reduction still makes sense for lazy, sharing-heavy programs, massive parallelism, and optimal reduction (exponentially fewer β-steps for some terms, but more bookkeeping per step).

**Conclusion:** the two are equally expressive. For strict, mostly first-order code, which includes
low-level code, the compiler targeting an ordinary CPU wins.

## 7. Laziness

Laziness is opt-in only: an explicit `Lazy a` type, or codata for streams and infinite structures
(see sections 3 and 5). Call-by-need by default means thunks, a shared graph and a GC, which is
the video's main complaint.

**Unresolved:** what does `Lazy a` cost without a GC? A thunk used exactly once (linear) never
needs caching, so it's just a closure. A shared thunk needs caching and therefore refcounting.

## 8. Overview: how the language works and what it fits

**Pure, strict, functional, compiled to native code with no GC and almost no runtime.**

| Area | Choice |
|---|---|
| Evaluation | Strict; laziness through `Lazy a` or codata |
| Polymorphism | Monomorphization, with copies merged by memory layout; `dyn` written explicitly |
| Functions | Known calls become `call`/`ret`; closures are `{code ptr, env}`, defunctionalized where possible |
| Memory | Linear/affine types by default, refcounting with reuse for sharing, arenas |
| Data | Unboxed by default, explicit `Box`, `bitdata` |
| Effects | `! MMIO`, `! IRQ`, `! Unsafe` etc. in function types |
| Control | Guaranteed tail calls and join points |

- **Best fit:** embedded systems and firmware, kernels and drivers, real-time code (audio, control, games).
- **Good fit:** compilers and interpreters, data pipelines, verified or safety-critical code.
- **Weak fit:** cyclic or heavily shared graphs (use arenas or indices), laziness-heavy code, fast prototyping, plugins and dynamic linking (would need Swift-style witness tables).

## 9. Why use it for kernels, drivers and firmware

**Compared with C:** linear types end use-after-free, double-free and leaks; algebraic data types
and exhaustive matching replace null pointers and unchecked unions; typed `bitdata` registers
replace macro bit-twiddling; undefined behavior is gone or explicit; effects show which functions
touch hardware.

**Compared with Rust, the real argument:**
1. **Linear, not affine.** A resource can't be silently dropped, so an interrupt must be acknowledged and a DMA buffer must come back:
   ```haskell
   startDma : Channel -o Buffer -o InFlight      -- consumes both
   waitDma  : InFlight -o (Channel, Buffer)      -- only way to get them back
   ```
2. **Effect types** make rules like "this IRQ handler doesn't allocate or block" checkable by the compiler.
3. **Purity** keeps the core logic (scheduling, page tables, parsers, file-system metadata) pure and testable, and much cheaper to prove correct. seL4's C proof took on the order of 20 person-years; Cogent was created to cut that effort for file systems.
4. **In-place reuse:** a pure `update state event` compiles to an in-place mutation.

**Costs:** no ecosystem (HALs, RTOSes, debuggers), no track record, a steep learning curve,
monomorphization compile times, and the C boundary is unsafe.

**Sweet spot:** high-assurance systems (medical, avionics, automotive, security kernels).

## 10. C interop: maximum usability with maximum safety

You can't make C itself safe. The goal is to keep unsafe C behind a small, marked boundary, and to
contain C bugs even when the C is called correctly.

**1. Direct header import** (like Zig's `@cImport`): the compiler embeds a C front end, so no
separate binding generator is needed.
```haskell
import c "libpng/png.h"
```

**2. Raw imports are `Unsafe`.** `Unsafe` is an effect that spreads to callers until a module
marked `trusted` takes responsibility for it, so `grep trusted` lists every audited boundary.
```haskell
extern "C" uart_read_raw : Ptr u8 -> usize -> i32 ! Unsafe
```

**3. Safe wrappers, inferred automatically where possible:**

| Signal in C | Inferred type |
|---|---|
| `_Nonnull` / `nonnull` attribute | plain pointer, not `Option` |
| `*_create`/`*_destroy`, `*_open`/`*_close` | linear handle |
| `(ptr, len)` parameter pairs | `Buf n` |
| `int` errors `< 0` | `Result` |
| `const T *` | borrowed, read-only reference |
| `__counted_by(n)` | length-checked array |

Gaps are filled by a per-library annotation file, shared like TypeScript's `.d.ts` files.
Hand-written wrapper example:
```haskell
trusted module Uart.Ffi
opaque type Handle
extern "C" uart_open  : u32 -> Ptr Handle ! Unsafe
extern "C" uart_close : Ptr Handle -> ()  ! Unsafe
open  : u32 -> Option Handle ! IO       -- NULL → Option, checked once
close : Handle -o () ! IO               -- must close exactly once
read  : &Handle -> Buf n -o (Buf n, Result usize Error) ! IO
```
Layouts use `repr C` and `bitdata`. C callbacks map directly onto closures: C's
`(fn, void *ctx)` pattern is our `{code ptr, env}`, with the environment either lent for the
call or handed over linearly.

**4. Sandbox by default.** Each C library is compiled into its own fenced-off memory region
(wasm-style compilation like RLBox, as in Firefox, or an MPU region on microcontrollers). Every
value coming out is `Tainted a` and must be checked before use:
```haskell
let w : Tainted u32 = png.get_width img
let width = w |> verify (\x -> x > 0 && x <= 16384)
```

**5. Trust tiers, one per import:**
```haskell
import c "libpng/png.h"   sandboxed      -- default: contained, tainted outputs
import c "vendor_hal.h"   trusted        -- direct calls, Unsafe, audited (needed for MMIO/IRQ code)
import c "crypto.h"       verified       -- trusted + contracts proven (Frama-C / VST)
```

**Extra protection when available:** compile the C with clang's bounds-safety mode
(`-fbounds-safety`); on CHERI hardware (Arm Morello), every pointer is checked in hardware.

Other options from cheapest to strongest: an MPU region, a separate process (seL4-style
microkernel isolation), or CHERI.

## 11. Translating C libraries and SDKs for zero dependencies

**Goal:** translate C libraries and SDKs into our language, so a kernel, driver or firmware build
needs no C toolchain. Removing the C toolchain is easy; making the translated code safe is hard.
Treat them as two stages.

**Prior art:** c2rust (works, but the output is almost all `unsafe`), Zig `translate-c` (mechanical,
weak on macros), Laertes (lifts raw pointers to references), DARPA TRACTOR and LLM-assisted
C → safe Rust (active research). A faithful translation is solved; a safe one is undecidable in
general and only partly automatable.

**Stage 1: mechanical translation into an unsafe C-level dialect** (raw pointers, mutable
locals, pointer arithmetic, all under `! Unsafe`). This alone gives zero dependencies. Verify it
with differential testing: run the original test suite against both the C build and the
translated build.

```c
int sum(const int *a, size_t n) {
    int s = 0;
    for (size_t i = 0; i < n; i++) s += a[i];
    return s;
}
```
```haskell
-- stage 1: faithful, unsafe
sum : Ptr i32 -> usize -> i32 ! Unsafe
sum a n = loop 0 0 where
  loop i s = if i < n then loop (i + 1) (s +% load (a +. i)) else s
```

**Stage 2: lifting passes, one function at a time**, each one removing the `Unsafe` effect:
```haskell
sum : &[i32] -> i32
sum xs = fold (+%) 0 xs
```

| Pattern found | Lifted to |
|---|---|
| `(ptr, len)` used only within bounds | slice `&[T]` |
| Pointer never written through | borrowed, read-only reference |
| `malloc`/`free` with a single owner | linear `Box` |
| `*_create`/`*_destroy` | linear handle |
| `int` error codes | `Result` |
| No writes to globals or through pointers | pure function |
| `volatile` access to fixed addresses | `! MMIO` with typed registers |

Code that can't be lifted stays unsafe, but **we own the compiler, so we sandbox it at
compile time** by inserting wasm-style bounds masks on its memory accesses. No RLBox or other
runtime is needed. LLMs propose lifts that static analysis can't prove; differential tests and
the type checker decide whether to accept them.

**Vendor SDK shortcut:** register definitions in microcontroller SDKs are generated from SVD
files (XML register descriptions). Generate `bitdata` and typed registers straight from the SVD
(like `svd2rust`) instead of translating the generated C. Only the logic layer (clock setup,
drivers, USB stacks) needs translating.

**Hard parts:**
- **Preprocessor:** keep `#ifdef` configuration as compile-time conditions in our language instead of translating after preprocessing (c2rust's biggest weakness).
- **Undefined behavior:** our semantics are defined, so behavior can differ from what the C compiler produced; differential tests catch the cases that matter.
- **Unusual C:** `setjmp`/`longjmp`, varargs, union type punning and computed `goto`. Join points handle `goto`; the rest goes to the unsafe dialect or gets rewritten by hand.
- **Inline asm:** keep it as our inline asm under an effect.
- **Startup code and linker scripts:** our toolchain produces the vector tables, `crt0` and memory layout.
- **Upstream updates:** the translation is a fork. Store lifting decisions and annotations separately, like patch files, and replay them on new releases.
- **Licensing:** translated code is a derivative work; the original license still applies.

**What "zero dependencies" means:** it removes the C compiler, the C toolchain and the
two-language boundary. You still have the code's logic, license and bugs, but the bugs are now
visible to our analysis and contained by the unsafe tier.

**Recommended pipeline:**
1. Generate register layers from SVD.
2. Translate everything else mechanically.
3. Verify with differential tests.
4. Lift progressively, starting with code that parses untrusted input.
5. Keep the section 10 import tiers for libraries not yet translated.

## 12. Backends: architectures and operating systems

**One compiler with several small backends, not one compiler per architecture.** The work is
mostly shared:

```
source → parse → types/effects/linearity → monomorphize → closure conversion → ANF
       → low-level IR (SSA)  → optimizations                    ← all shared (~80–90%)
       ──────────────────────────────────────────────────────
       → instruction selection → register allocation → encoding → object file
                                  ↑ per architecture (~10–20% each)
```

**Per architecture:** instruction selection, the register description (which registers a called
function must preserve), the calling convention, and instruction encoding. The register
allocation algorithm itself is shared.

**Make each backend a description, not hand-written code:**
- Go's `.rules` files map IR patterns to instructions; Go supports about ten architectures this way with no LLVM. This is the closest model to ours.
- Cranelift's ISLE pattern DSL covers x86-64, AArch64, RISC-V and s390x.
- QBE: amd64, arm64 and riscv64 in roughly 10–15k lines of C, showing how small a backend can be.

Adding an architecture then means writing a register/calling-convention table, a few hundred
lines of selection rules, and an instruction encoder, checked against the system assembler. Once
the IR exists, that takes **about 2–6 weeks per backend**.

**Four instruction sets cover kernels and firmware:**

| Family | ISA | Where |
|---|---|---|
| ARM | AArch64 | Macs, phones, servers |
| ARM | Thumb-2 (ARMv7-M / v8-M) | Cortex-M microcontrollers (most firmware) |
| x86 | x86-64 | PCs, servers |
| RISC-V | RV64 / RV32 (one set of rules) | Embedded, some servers |

**Can't be abstracted away** (small per-architecture modules, a few thousand lines each in a
kernel): inline asm, interrupt/exception entry and context switching, MMU/MPU formats, and
atomics. ARM and RISC-V are weakly ordered and x86 strongly ordered, so the language offers one
portable atomics API that each backend implements.

### Operating systems and cross-compilation

**Targets are named by triple:**
```
aarch64-apple-macos        ← your Mac
x86_64-linux-gnu
x86_64-windows-msvc
riscv64-linux
thumbv7em-none-eabihf      ← Cortex-M, no OS
```
**Host** (where the compiler runs) and **target** (what it emits) are independent, so any host
can build for any target. Zig shows this works, and we get it for the same reason: no C
toolchain dependency (section 11).

**The per-OS layer is small:**

| Concern | Example |
|---|---|
| Executable format | Mach-O (macOS), ELF (Linux, BSD, firmware), PE/COFF (Windows), raw binary |
| Calling convention differences | Windows x64 uses different argument registers; Apple ARM64 deviates slightly from the standard |
| Talking to the OS | Linux has stable syscalls; macOS/Windows require the system library (`libSystem`, `kernel32`) |
| Startup, thread-local storage, unwind/debug info | different formats on each OS |
| Loader requirements | macOS ARM64 binaries must be code-signed (the system `ld` ad-hoc signs them automatically) |

Three object-file writers (Mach-O, ELF, PE) cover everything. The main target for kernels and
firmware is **freestanding** (`none` in the triple: no OS, no loader, raw ELF or binary), which
is also the simplest.

```
          one frontend + IR (shared)
                    │
   ┌────────┬───────┴─────┬──────────┐
 AArch64  Thumb-2     x86-64     RISC-V         ← 4 architecture backends
   │         │           │          │
 macOS    none        Linux     Linux/none      ← small OS layers, mixed and matched
 Linux               Windows
 none                none
```

**Mac notes:** Apple Silicon uses the AArch64 calling convention (arguments in `x0`–`x7`, return
address in `x30`, 16-byte-aligned stack). macOS syscalls aren't a stable interface, so go
through `libSystem`.

**Build order:**
1. AArch64 only, written directly, to see results on the Mac quickly.
2. Introduce the shared IR and move AArch64 behind it.
3. Add x86-64, RISC-V and Thumb-2 as rule files. Verify by running the same tests on every target and comparing outputs, on real hardware or in QEMU.

## 13. Real-time safety

"Real-time safe" means two things:
- **Memory safety:** already covered by linear types, effects and sandboxing.
- **Timing safety:** every deadline is met. The language can make timing *analyzable* and rule out the usual hazards. Proving deadlines still needs analysis tools.

**What the design already gets right:**

| Hazard | Typical source | Our language |
|---|---|---|
| GC pauses | Java, Go, Haskell, OCaml | No GC |
| Hidden runtime work | thunks, runtime dictionaries, lazy init | strict evaluation, monomorphization, no thunks unless you write `Lazy` |
| Hidden allocation | closures, boxing | unboxed by default, explicit `Box`, closures on the stack unless they escape |
| Indirect calls that are hard to analyze | virtual dispatch, function pointers | defunctionalization turns them into a `switch` over a known set |
| Unexpected side effects | any function can do anything | effects in every function's type |

With no hidden runtime, the binary is plain code, so worst-case execution time (WCET) tools that
work on binaries (e.g. aiT) handle it like C.

**The key piece is a real-time effect discipline.** Interrupt handlers and hard real-time tasks
get types that exclude `Alloc`, `Block` and `Diverge`, checked through every call they make:
```haskell
-- effects: Alloc (heap allocation), Block (may wait), Diverge (may not terminate)
controlLoop : &Sensors -> &mut Actuators -> () ! MMIO     -- no Alloc, no Block, no Diverge
controlLoop s a = ...
  -- calling anything with ! Alloc or ! Block here → compile error
```

**Pieces still needed:**
1. **Refcount cascades:** freeing the last reference to a big structure takes unbounded time. Real-time code uses linear types and arenas only (constant-time free), or decrements are deferred to a background task. Refcounting carries `Alloc`, so the compiler keeps it out of real-time code automatically.
2. **Termination and loop bounds:** check `Diverge` with a totality checker (as in Agda and Idris); sized types bound iteration counts; non-tail recursion needs a bounded stack depth.
3. **Execution cost in the types (optional):** resource-aware typing (RAML, automatic amortized resource analysis) infers bounds such as `3n + 5` steps. A WCET tool still supplies the cycle counts on real hardware.
4. **No deadlocks or priority inversion by construction:** RTIC's priority ceilings (the Stack Resource Policy), expressed with linear resource tokens and priority effects.
5. **No laziness in real-time code:** `Lazy` carries `Alloc` or `Diverge`.

**What no language guarantees alone:**
- **Schedulability:** whether all tasks meet their deadlines together needs rate-monotonic or response-time analysis.
- **Hardware timing:** caches, pipelines and multicore interference make cycle counts uncertain; hard real-time systems use simple cores, cache locking, or conservative WCET tools.
- **Certification:** DO-178C (avionics) and ISO 26262 (automotive) need a qualified toolchain and process, which takes years.

**Compared with alternatives:** C relies on MISRA rules alone. Ada/SPARK with the Ravenscar profile
is the gold standard. Rust + RTIC gives memory safety plus deadlock-free scheduling. Ours aims
for all of that plus compiler-checked no-alloc, no-block and guaranteed-termination effects, and
pure control logic that can be proven correct.

**Summary:** at compile time, the compiler rejects any program where a real-time path might
allocate, block, loop forever, deadlock or corrupt memory, and the binaries can be analyzed by
standard timing tools. Meeting the actual deadlines still needs worst-case timing and
schedulability analysis.

## 14. Verification and security firmware

**Question:** could companies like NVIDIA (which uses SPARK/Ada for some security-critical
firmware) use this language for secure and measured boot, signed firmware, hardware roots of
trust, memory isolation, and confidential computing?

**What the design proves today, through types:** memory safety, no leaked or duplicated
resources (linear types), and no allocation, blocking or divergence where forbidden (effects).
**Not yet:** functional correctness (e.g. "the verifier accepts exactly the valid signatures"),
which needs specifications plus a prover. Even a full proof only holds relative to the
specification and a model of the hardware; glitches and side channels are outside it.

**Why companies pick SPARK:** automatic proof that runtime errors can't occur (no overflow, no
out-of-bounds access, no division by zero, mostly push-button through SMT solvers),
pre/postconditions and loop invariants proven by GNATprove, maturity with qualified tools and
AdaCore support, and familiar imperative style. A new language must match the first two, and
eventually the rest.

**Where our design could do better:**

| Advantage | Why it matters |
|---|---|
| Purity | Proofs are much easier without mutable state, which consumes most of the effort in SPARK proofs |
| Linear types | Keys, buffers and hardware resources can't be duplicated, leaked or used after release; secrets are wiped exactly once |
| Effect types | "The boot verifier only touches the hash engine's MMIO" becomes a compiler-checked fact |
| Constant-time typing (to add) | A `Secret a` type that code can't branch on or use as an index, stopping timing side channels (as in Jasmin and FaCT) |
| In-place reuse | Pure code still compiles to tight firmware |
| RISC-V backend | Much current security-processor firmware runs on RISC-V cores |

**What we'd have to add:**
1. **A specification and proof layer:** refinement types (Liquid Haskell, F*), e.g. `{ n : u32 | n < len buf }` checked by an SMT solver, for automatic proof that runtime errors can't happen. Dependent types (Lean or Idris style) only for the hard proofs.
2. **A trustworthy compiler:** a verified compiler (CompCert, CakeML; very expensive) or, more realistically, **translation validation** (check each compiled output against its source).
3. **Constant-time and information-flow types** for crypto and key handling.
4. **Verified building blocks:** hashing, signature verification, measurement logging. HACL* has shipped in Firefox and Python's `hashlib`, so this is achievable.
5. **Tool qualification and certification evidence.**
6. **Interop with existing C/Ada code** (sections 10–11).

**Competition (other verification systems, not C):** SPARK/Ada (incumbent), Rust + verifiers
(Verus, Kani, Creusot, Aeneas), F*/Low\* → C (HACL*, EverParse), Jasmin (constant-time crypto in
asm), seL4-style Isabelle proofs (strongest, very expensive).

**Pitch:** the purity of F\*, the low-level control of SPARK, and Rust-style ownership in one
language that compiles directly to RISC-V firmware.

**Adoption path:**
1. Research prototype with refinement types, demonstrated on one component, e.g. a verified secure-boot image verifier for RISC-V.
2. Published results: proofs, performance against C/SPARK, constant-time guarantees.
3. One narrow component in production (a parser or boot verifier) alongside existing code.
4. Qualification, support, and a company behind it (the AdaCore role).

From here to step 3 is realistically 5–10 years, with a team.

**Bottom line:** the architecture fits the domain well, arguably better than SPARK for boot and
crypto code. Adoption depends on the proof layer, a trustworthy compiler, and a track record.

## 15. Testing with emulators

All four backends (section 12) can be tested on the Mac and in CI without hardware.

| Tool | Emulates | Use for |
|---|---|---|
| QEMU system mode (`qemu-system-riscv64`, `-riscv32`) | A whole machine (`virt` board) | Freestanding/kernel target: boot an image, print over UART |
| QEMU user mode (`qemu-riscv64`) | CPU only, Linux programs | Hosted RISC-V Linux binaries. **Linux hosts only**; on a Mac use Docker (`--platform linux/riscv64`) or a Linux VM |
| Spike | Official RISC-V reference simulator | Golden reference to rule out emulator bugs |
| Renode | Whole microcontroller boards with peripherals | Firmware CI, multi-device simulation |
| Sail RISC-V model | The formal, executable ISA spec | Checking against the official ISA definition (links to section 14) |

QEMU also covers Cortex-M boards (e.g. `mps2-an385`, for Thumb-2), x86-64 and AArch64.

**Workflow:**
```sh
brew install qemu llvm

keelc --target riscv64-none-elf hello.kl -o hello.elf
llvm-objdump -d --triple=riscv64 hello.elf                        # inspect output
qemu-system-riscv64 -machine virt -nographic -bios none -kernel hello.elf
qemu-system-riscv64 -machine virt -nographic -bios none -kernel hello.elf -s -S
#   ↑ waits for a debugger: connect lldb/gdb to localhost:1234
```
On QEMU's `virt` machine the UART is a 16550-compatible chip at `0x1000_0000`. The first "hello
world" is a few `MMIO` writes there, a good first test of the `bitdata`/`MMIO` design.

**Strategy:**
1. **Differential testing:** the same test programs on every target (native AArch64 on the Mac, QEMU for the others); all outputs must match.
2. **Encoding checks:** compare our instruction bytes against LLVM's assembler.
3. **CI:** everything runs headless, so every commit is tested on all four architectures.

**What emulators can't tell you:**
- **Timing:** QEMU isn't cycle-accurate, so it's no use for WCET (section 13).
- **Memory-ordering bugs:** weak ordering on RISC-V/ARM may not show up when emulated; test atomics on real chips.
- **Peripheral quirks:** emulated devices are simplified, and real chips have errata.
- **Security hardware:** fault injection, side channels, root-of-trust features.

**Cheap real hardware for final checks:** ESP32-C3/C6 and WCH CH32V003 (RISC-V
microcontrollers), Raspberry Pi Pico 2 (Cortex-M33 and RISC-V cores), StarFive VisionFive 2 and
Milk-V (RISC-V Linux boards).

**Flow:** develop and run CI in emulators; confirm timing, concurrency and peripherals on one or
two boards.

## 16. Design decisions

| Area | Decision |
|---|---|
| References | Second-class `&` / `&mut` (inout = pure state passing) |
| Local mutation | Linear state passing + `&mut`/`var` sugar + in-place reuse; no ST |
| Effects | Koka-style rows; capabilities + immediately-resuming handlers only; signatures required on exported functions |
| Errors | Linear `Result` + `?`; `Panic` effect; panic handler with reset, a persistent log, and a reset counter leading to safe mode |
| Overflow | Checked by default; proven safe operations have no check; `+%` `+|` `+?` explicit |
| Memory exhaustion | Arenas sized at compile time where possible → otherwise `Result` → panic as last resort |
| Concurrency | Pure parallelism free; linear handoff, priority ceilings, channels, small atomics API |
| Ad hoc polymorphism | Explicit dictionaries (codata values) + monomorphization |
| Type-level numbers | Comptime integer parameters + refinement types; no full dependent types in the core |
| Interfaces | Codata |
| SIMD | Fixed and scalable vector types in the standard library + per-architecture intrinsics |
| Static data | Comptime everything; placement annotations; global state handed to `main` as linear resources |
| Metaprogramming | Zig-style comptime, pure and sandboxed; generics type-checked before use |
| Tooling | Query-based compiler library from day one |

### References and borrowing
Second-class references (Hylo's mutable value semantics, Austral): they can't be stored in
structs or returned. **Purity is preserved:** `&T` behaves like passing a copy, and `&mut T`
behaves like passing the value in and getting a new value back.
```haskell
push : &mut Ring -> u8 -> ()          -- what you write
push : Ring -o u8 -> Ring             -- what it means: pure state passing
```
Cost: a driver can't hold `&Bus`. It owns a linear `Bus` handle and hands it back, or uses
indices. That fits hardware's single ownership. Raw pointers remain in the unsafe dialect.

### Local mutation
State passing, not ST. ST gives real mutable variables in a sealed region and needs a higher-rank
type. State passing stays pure; linear types stop the old state from being reused, so in-place
reuse turns the "recreate" into an update. State machines are `State -o Event -> State`.
```haskell
type Ring = { buf : [u8; 64], head : u6, tail : u6 }

drain : &mut Ring -> &Uart -> () ! MMIO
drain r u =
  if r.head != r.tail then
    write u.data r.buf[r.tail]
    r.tail += 1          -- sugar for producing the new state
    drain r u            -- tail call → loop
```

### Effects
- Koka-style effect rows give effect polymorphism (a generic `map` accepts effectful functions).
- Capabilities, plus **only immediately-resuming (tail-resumptive) handlers**, which compile to plain calls. General handlers that capture continuations are not allowed in freestanding code.
- Bonus: swap the `MMIO` handler for a mock, so driver logic runs in tests and the REPL on the Mac.
- Inference: infer inside function bodies and for private helpers; require effect signatures on exported, top-level functions.

### Errors
- `Result` is **linear**: it must be handled, propagated (`?`) or explicitly discarded.
- **Panic = reset, with protection.** A blind reset risks boot loops, and attackers can glitch the device repeatedly. Every freestanding program must define a panic handler. The default writes the reason to RAM that survives the reset, resets, counts consecutive resets, and enters safe mode or halts after N.
- `Panic` is an effect, so verified and real-time code can require "no Panic".
- **Checked overflow + refinement types (like SPARK):** a proven-safe addition gets no check and no `Panic`; otherwise the compiler inserts a check and adds `Panic`. Explicit operators: `+%` wrap, `+|` saturate, `+?` returns `Option`.
- **Out of memory:** size arenas at compile time so it's provably impossible; otherwise allocation returns `Result`; panic only as a last resort.

### Concurrency
Purity makes pure computation race-free and parallel, which covers most code. Firmware
concurrency is mostly shared hardware and shared state (interrupt handler ↔ main loop, DMA,
multicore ordering), which is effectful by nature. Tools:
- linear handoff of resources between contexts
- RTIC-style priority ceilings (section 13), so no races and no deadlocks
- channels between cores
- a small atomics API with a defined memory model

**Done (hosted): a pure event loop**, `std.loop`. With tail-resumptive handlers there are no
continuations to suspend a thread with, so a concurrent program is a pure state machine
`step : s -> Event -> (s, List Command)`. `loop.run` owns the sockets and timers: it polls, turns
readiness into events and carries out the commands through the built-in `Net` effect. It is
one thread with no shared state, its connections are numbers that are never reused, and
`step` can be tested by feeding it a list of events. The same shape fits firmware later, with
interrupts as events.

### Ad hoc polymorphism and interfaces
Explicit dictionary passing + monomorphization. A dictionary is a codata value and is inlined at
zero cost. No global instance resolution and no orphan instances. Usage: `sort intOrd xs`.

Codata defines interfaces by their operations:
```haskell
codata Serial = {
  send  : &mut Self -> u8 -> () ! MMIO
  ready : &Self -> Bool         ! MMIO
}

uart0 : Serial = cocase {               -- an implementation, defined by its operations
  send  s b = write UART0.data b
  ready s   = (read UART0.status).tx_ready
}

log : Serial -> &mut Self -> Str -> ()   -- generic over any Serial
```
Interfaces, dictionaries, streams and state machines become one feature. Dispatch is static
unless written as `dyn`.

### Type-level numbers
Comptime-known integer parameters (`Buf n`, like Rust const generics or Zig) for sizes, plus
refinement types (`i < n`, checked by SMT) for relationships between values. No full dependent
types in the core; they stay a possible later layer for proofs.

### SIMD
Portable vector types in the standard library (`Vec 4 f32`, like Rust `std::simd` or Zig
`@Vector`) plus per-architecture intrinsic modules. RISC-V's vector extension and ARM's SVE have
lengths only known at runtime, so the language needs both fixed-width (`Vec n T`) and scalable
vector types. Targets without SIMD get scalar fallback code.

### Static data
Everything that can be computed at compile time is (tables, CRCs, register maps, config, all
placed in flash). Placement and alignment annotations exist for linker sections, and there are
no initialization-order problems. Mutable global state is a linear resource handed to `main`
once (the embedded "peripherals singleton" pattern), so there are never two handles to one timer.

### Compile-time computation
Zig-style comptime, but **pure and sandboxed** (the video's Template Haskell lesson): no
arbitrary IO, only build-declared inputs such as SVD files; deterministic and reproducible.
Generic code is type-checked before instantiation, unlike Zig.

### Stack bounds, REPL, syntax, tooling
- The compiler computes each function's maximum stack usage (links to section 13).
- A fast interpreter/REPL is planned from the start to offset slow monomorphized builds; the section 5 evaluator is its seed.
- Type annotations are required on top-level functions, with an investment in clear error messages.
- Rust-style editions instead of per-file extension flags.
- The compiler is a query-based, incremental library from day one (like rust-analyzer/Salsa), with source locations everywhere. The language server, REPL, error messages and DWARF debug info reuse it; formatter and package manager follow.

## 17. Timeline / roadmap

Rough effort estimates for building the compiler together. They depend mostly on hours per week:
code gets written fast, but understanding and steering each part takes time.

| # | Milestone | Includes | Rough effort |
|---|---|---|---|
| **M0** | Toy compiler | Section 5 evaluator → λ-terms + ints → ANF → closure conversion → AArch64 asm, assembled and linked with the Mac's `as`/`ld`; closures in a never-freed bump arena | A few sessions (~1–2k lines). **Done:** `Keel.Lower` + `Keel.AArch64`, differential-tested natively |
| **M1** | Small real language | Parser, type inference, ADTs + pattern matching, monomorphization, guaranteed tail calls, simple stack-based codegen, a syscall-only runtime; shared IR introduced | 2–6 weeks. **Done:** `keelc` (parser + inference, `spec/surface.md`), data/case/pairs/codata, all integer widths, tail calls, typed result printing; runtime still uses libSystem (`printf`, `write`, `exit`), not raw syscalls |
| **M2** | No-GC memory model | Linear/affine checking, second-class references, refcounting with in-place reuse, arenas | 1–3 months (close to research). **Done:** linear checking and second-class refs (Keel Core stages 1 and 3); Perceus-style reference counting with in-place reuse, free lists and a leak check on every native test (`spec/memory.md`). Arenas: `arena (\u. e)` frees everything allocated inside at once, accepted only when nothing can escape (`spec/memory.md`); inferred borrowed parameters (as in Lean). Not yet: arenas sized at compile time |
| **M3** | Systems features | Effects (`MMIO`, `Unsafe`, `Alloc`, `Panic`…), `bitdata`, `repr C`, inline asm, C header import, freestanding mode | 1–3 months. **Done:** native effect handlers, `MMIO` effect, `bitdata`, bitwise ops, `as` conversions, hex literals, freestanding RISC-V back end on QEMU virt (`keelc qemu`); x86-64 Linux back end (`--target x86_64`, `Keel.X86`, with the ARM back end's optimizations and an SSE4.1 vector loop), the test suite runs on a real x86 machine over ssh (`KEEL_X86_HOST`); whole test suite runs on all three targets. Not yet: `Unsafe`/`Alloc` effects, `repr C`, inline asm, C header import |
| **M4** | Fast output | SSA, register allocation, inlining, defunctionalization; our own Mach-O/ELF writers instead of `as`/`ld` | 3–12 months to be decent; C `-O2` speed takes years. **Done so far:** known-arity calls, callee-saved register allocation, specialization on constant dictionaries and functions (closed λs lifted) + inlining + dead-code removal (`Keel.Opt`); 1.3–4.4× faster (`spec/perf.md`, `ref/bench/`). Self tail calls are loops; constructors without fields are shared static blocks; the tag lives in the block header; AArch64 operands straight from registers and compare-and-branch; registers by graph colouring, self tail calls as parallel moves; reductions over arrays vectorized (NEON); arrays grow in place; a block's first narrow field lives in its header (layout ids, 21-bit counts); arrays of narrow elements take 4 bytes each; range analysis removes overflow and bounds checks it proves unnecessary (`Keel.Range`). Measured against Goose, C++ and Rust in `ref/bench/goose/results.md`. Not yet: SSA, live-range splitting, narrow fields, defunctionalization of capturing λs, own object writers, the same code improvements on RISC-V |
| **M5** | Usable by others | Standard library, error messages, build tool, language server, debugger support, self-hosting | 1+ year. **Started:** error messages with file:line:col and the source line; a prelude in Keel (lists, strings, printing) with string literals; `/` `%`; `putc`; modules (`import`, `private`) and projects (`keel.project`, `keelc new`/`build`/`run`); a language server (`keelc lsp`: diagnostics while typing, hover types of top-level names, go-to-definition). namespaces (imports scope names; `console.greet`, `uart.Status`, `import a.b as q`). debug info (`keelc build -g`: DWARF line table and function names for lldb). A standard library: `std.map` (AVL maps), `std.array` (growable arrays, updated in place when unshared), `std.string`, `std.file` (reading files by name, effect `Files`), input (`getc`, `readAll`, effect `Input`). Character literals (`'a'`). `&&` `||` `!=` `>` `<=` `>=` `not`, literal patterns and `_ ->` defaults in `case`. Self-hosting begun in `ref/selfhost/`: the lexer and parser in Keel; the test suite checks that the parser prints the same syntax tree as keelc's for every `.kl` file in the repo. Not yet: local types in the language server, variable values in the debugger, debug info on RISC-V, source positions in the self-hosted parser, the rest of the self-hosted compiler |

For comparison: Zig started in 2015 and Roc in 2019, and neither has reached 1.0; Koka has been in
development for over a decade.

**Updates from later sections:**
- **Before M1:** write down the core language formally (section 16); M1 and M2 depend on it.
- **From M1:** build the compiler as a query-based library (section 16), and grow the section 5 evaluator into the REPL alongside it.
- **After M1:** add x86-64, RISC-V and Thumb-2 as rule-file backends, 2–6 weeks each (section 12), tested in QEMU (section 15). A first RISC-V "hello world" over the `virt` UART fits naturally with M3's freestanding mode.
- **Long term:** the verification layer (refinement types, translation validation, constant-time types, section 14) and C translation (section 11) are multi-year efforts beyond M5.

**Suggested path:** M0 first, to see λ compile and run on the Mac. Then M1. Then choose between M2
(the memory model, most novel) and M3 (running on a microcontroller, most fun).

## 18. Real hardware: Raspberry Pi Pico 2 W (planned)

Goal: run Keel firmware on real silicon, not only QEMU. The user has a Pico 2 W.

**The board.** RP2350 chip: two ARM Cortex-M33 cores and two RISC-V Hazard3 cores (32-bit,
RV32IMAC plus extensions); the boot image selects the architecture. Start on the RISC-V cores,
since Keel already has a RISC-V back end. On the "W" boards the onboard LED is wired to the
wireless chip (CYW43439), not to a GPIO, so blinking it is a project of its own.

**Getting output.** The language isn't the blocker: Keel firmware already writes bytes to a UART
through `MMIO` (`ref/examples/firmware/hello.kl`). The options:
- **Raspberry Pi Debug Probe or a USB-to-serial adapter on GPIO0/GPIO1 + GND (preferred).** It
  appears on the Mac as `/dev/cu.usb…`; Claude can capture it non-interactively (`stty` +
  a background read) and check the same `result:` / `keel-stats:` lines as on QEMU. The Debug
  Probe also flashes and resets over SWD (OpenOCD), so no BOOTSEL button presses.
- **An external LED and resistor on a GPIO pin**: enough for a first "it runs" blink, but no
  results can be read back.
- **Serial over the Pico's own USB port** needs a USB device stack (USB CDC; the C SDK uses
  TinyUSB). Possible later, but a large project.

**Work needed:**
1. **32-bit RISC-V output (RV32).** The back end is RV64, and Keel assumes 64-bit values. On
   RV32, either implement `i64` with register pairs and 32-bit heap words, or start with `i64`
   unsupported. This is the largest piece.
2. **Boot image:** the RP2350 boot ROM needs an image definition block, packaged as UF2; flash by
   copying to the BOOTSEL drive or with `picotool` (`brew install picotool`).
3. **Startup code:** release peripherals from reset, configure clocks, select the pin functions
   for UART0, set the baud rate. Ordinary `MMIO` register writes, a natural first Keel driver.
4. **Tests:** run the native test programs on the board over serial, like the QEMU runs.

**Decision pending:** which output path. Waiting for an adapter or Debug Probe.

## 19. Open threads / next steps

- [ ] Work out what opt-in `Lazy a` costs without a GC (section 7).
- [ ] Prototype C header import and the `Unsafe`/`Tainted` effects (section 10).
- [ ] Design the unsafe C-level dialect and a stage-1 C → dialect translator (section 11).
- [ ] Design the real-time effects (`Alloc`, `Block`, `Diverge`) and the termination checker (section 13).
- [ ] Design refinement types and constant-time `Secret a` typing; choose translation validation or a verified compiler (section 14).
- [x] First RISC-V milestone: "hello world" over the QEMU `virt` UART (section 15). Done in M3: `keelc qemu ref/examples/firmware/hello.kl`.
- [ ] Run Keel on the Pico 2 W (section 18): RV32 back end, RP2350 boot image and startup, UART output through a Debug Probe or USB-serial adapter.
- [x] Write the core calculus formally: linear types + second-class refs + effects + codata (section 16). Done: `spec/core.md` (Keel Core, stages 1–4) with the Haskell reference checker/evaluator in `ref/` (`cd ref && cabal test`).
- [x] Turn the evaluator from section 5 into a tiny compiler: λ-terms → ANF → closure conversion → ARM64 asm that assembles and runs on this Mac. Done (M0): `ref/src/Keel/Lower.hs` + `AArch64.hs`, checked against the reference evaluator by `ref/test/Native.hs`.
- [ ] Deep dive: closures and defunctionalization (eval/apply, partial application).
- [ ] Deep dive: Perceus refcounting and reuse (pure code compiled to in-place mutation).
- [ ] Deep dive: linear types, affine types, and QTT as a replacement for the GC.
- [ ] Deep dive: recursion (`fix`), tail calls, and join points.
