# Keel on the GPU: proposal

**Status: proposal; G1 partly implemented (f64).** Drafted 2026-10-30. Syntax in G2–G4 is a sketch
and hasn't been through `keelc`; nothing of G2–G4 is implemented.

Keel has no GPU target and no roadmap item for one. It has `f64` (G1, below) but not yet `f32`. This file proposes the smallest path from here to compute kernels written in Keel,
in four steps that are each useful on their own.

## Fit with Keel's goals

Keel is for systems code: operating system kernels, firmware and drivers. The word *kernel*
means two things here, and only one of them is central to that goal:

- **A GPU driver is ordinary CPU code**: device registers, memory mappings, DMA, command
  buffers, interrupts. It needs what Keel already has or is building (`MMIO`, `bitdata`,
  linear resources, handlers for mock devices), not GPU code generation.
- **A compute kernel runs on the GPU.** C, Rust and Zig are systems languages without
  targeting GPUs out of the box. Keel doesn't need GPU kernels to meet its goal.

So G2–G4 are an **optional track**, driven by one real workload, and should not take priority over
driver-side work (DMA, interrupts, page tables). G1 is different: systems programs use
floating point outside OS kernels (audio, sensors, control loops), and Keel needs it anyway.
It also fits Keel's effect system. OS kernels usually forbid the FPU outside marked regions
(Linux on x86 requires `kernel_fpu_begin()`), and an effect could make that a type error,
for example rejecting float code in an interrupt handler. That is a possible extension, not part of G1.

## Why one language for host and device

The benefit is not pairing a driver with kernels. A driver runs anyone's compiled kernels,
and the two are written by different people. It is pairing an **application** with its
kernels. CUDA C++ (host and device code in one file) won largely for this reason. SYCL,
CUDA.jl and Mojo work the same way. Metal, GLSL and WGSL keep separate shader languages.

What one language gives an application like energy-timestral:

- **One definition of shared layouts.** Its `Params` record is declared in `kernels.wgsl`
  and again in `gpu.rs`, and the two must agree byte for byte, including uniform alignment.
  A mismatch gives wrong numbers silently. One definition, laid out by the compiler for both
  sides, removes that class of bug.
- **The same functions on both sides.** Pure helpers (`dot`, SiLU, RMSNorm) run on the CPU
  in `keelc run` for testing and on the GPU for speed.
- **A checked boundary.** The compiler can check that a dispatch passes the buffers and
  parameter types the kernel expects. Today a wrong binding is a runtime error at best.

The cost every such language pays: device code is a **subset** (no allocation, no deep
recursion, no I/O, no indirect calls), so there are two dialects. CUDA marks the boundary with
`__device__` attributes and finds violations late. In Keel, effect rows already say what a
function may do. A function without `IO`, `Files`, `Net` or `MMIO` that doesn't allocate can
run on either side, and one that does is rejected by an ordinary type error (G2). Linear types
cover the host side's main bug class, leaked or released-then-used buffers (`Buf` in G4).

## The workload

The driving example is `energy-timestral` (`src/kernels.wgsl`, 68 lines): an inference port
of the Timestral time-series transformer, run through wgpu on an Intel UHD 600 (Vulkan) and
on Apple GPUs (Metal). It is one WGSL entry point with an `op` switch:

| Op | Computation | Needs |
|---|---|---|
| 0 | linear layer: bias + row · weight row | `f32` `+ *`, a counted loop |
| 1 | RMSNorm | `inverseSqrt`, `u32 → f32` |
| 2 | residual add | `+` |
| 3, 5 | SiLU and gated SiLU | `exp`, `/` |
| 4 | fused SwiGLU | `exp`, index arithmetic |
| 6 | rotary embedding | `pow`, `sin`, `cos`, a branch on the dimension |
| 7 | attention scores with mask | a loop, `sqrt`, a constant (`-1e30`) |
| 8 | stable softmax and value sum | two loops, `max`, `exp` |

Every op has the same shape, which keeps the first version small:

- one invocation per output element `i`, writing `z[i]` exactly once;
- read-only input buffers (`a`, `b`, `c`) and a uniform parameter record (`p`);
- `u32` index arithmetic, `f32` arithmetic and builtins, bounded loops and branches;
- no workgroup shared memory, barriers, atomics, subgroups or `f16`.

Host side: `src/gpu.rs` (270 lines of Rust) creates buffers, binds them, dispatches
`ceil(count / 64)` workgroups of 64, and reads results back. The acceptance test is
`scripts/parity.py`: GPU output against the original PyTorch model at `rtol=1e-3, atol=1e-3`
on the quantiles.

## G1: floating point (CPU only)

**Status: f64 implemented (2026-11-02)** as below, except: integer literals never become
floats (write `1.0`), result values print as their bit pattern, `string.fromFloat` gives 17
significant digits rather than the shortest form, and RV32 has no floats yet. `f32` is next: it
needs a 4-byte array element kind that isn't sign- or zero-extended.

Add `f32` and `f64` as base types of kind `Free`, beside `i8 … u64`.

| Feature | Proposal |
|---|---|
| Literals | `1.5`, `1e-30`, `-2.0`; width inferred from context, `f64` otherwise (like `i64`) |
| `+ - * /` | IEEE 754 round-to-nearest, **effect `{}`**: no overflow or division panics (results are `inf` or `NaN`) |
| Comparisons | `== != < <= > >=` return `Bool`, IEEE semantics (`NaN` compares false; `!=` true) |
| `e as τ` | int → float rounds to nearest; float → int **saturates**, `NaN` → 0 (Rust's rule; check that the generated WGSL matches it for out-of-range values) |
| Builtins | `sqrt`, `exp`, `log`, `pow`, `sin`, `cos`, `min`, `max`, `abs`, `floor` in a `std.float` module |
| Printing | `string.fromFloat`, shortest round-trip form |
| `Array f32` | already allowed: `f32` is `Free` |

Back ends: AArch64 FP/SIMD registers (`s`/`d`), SSE2 on x86-64, and the F/D extensions on
RISC-V. Floats are passed in FP registers, so the register allocator needs a second class;
calls follow each platform's C ABI. Transcendentals call the C library's `libm` (RISC-V
freestanding: a small bundled implementation, or `UnsupportedOnTarget` at first).

Evaluator: Haskell's `Float` and `Double` are IEEE single and double. Arithmetic and `sqrt`
are correctly rounded everywhere, so `run` and `build` must agree **exactly** on them, as
today. Transcendentals are not correctly rounded by `libm`; the evaluator should call the
same C functions through the FFI so the exact-match rule still holds on one machine.

Core: a new rule like §5's `Bits`, with effect `{}` for float arithmetic. The metatheory is
unchanged: these are primitives with ordinary typing rules.

Why first: everything else depends on it, and it removes a CPU limitation on its own.
energy-timestral computes its metrics in checked fixed point because Keel has no floats.

## G2: the kernel subset

A kernel is a definition marked `kernel`. It is type-checked as ordinary Keel and runs in
the evaluator as ordinary Keel, so every kernel is testable with `keelc run`. On top of
that, the kernel checker enforces what a GPU can execute:

| Rule | Reason | Existing machinery |
|---|---|---|
| Fully monomorphic after `Mono.hs`, no closure values left | no indirect calls on the GPU | Mono, known-arity calls (M4) |
| No allocation: no `box`, recursive data, `Array` construction or `arena` | no heap | the lowering already identifies allocation sites |
| Recursion only as tail calls, compiled to loops; no mutual non-tail recursion | no call stack | tail calls already compile to jumps |
| Effects ⊆ `{Panic, Diverge}` | no I/O, files, net or MMIO on the device | effect rows: a kernel's type says so |
| Buffers only as `&` parameters | read-only, can't escape the invocation | second-class references, §3 `RefEscape` |
| Non-recursive data and pairs are flattened to scalars | no pointers | layout templates (§4.4) |

**Race freedom by construction.** A kernel has the type

```
kernel k : &Buf τ₁ -> … -> &Buf τₙ -> P -> u32 ->{Panic, Diverge} σ
```

where the last argument is the invocation index and the **result is the output element**.
`dispatch` writes `out[i] = k … i` for every `i < count`. Kernels can't write to a buffer at
all, so two invocations can't race, and no ownership analysis is needed for the first version.
All nine energy-timestral ops fit this shape. Writes to arbitrary indices (`&mut Buf` plus a
disjointness proof) come later, together with shared memory and barriers.

**Panic on the device.** Keel arithmetic on integers is checked, and indexing is
bounds-checked; dropping those checks in kernels would make `run` and the GPU disagree. Instead,
a panicking invocation sets a per-dispatch fault word (an atomic store of the first fault code)
and returns `0`; the host checks the word after the dispatch and reports the panic. The checks
cost a compare and branch each. Wrapping operators (`+%`) and an unchecked `gpu.get` variant (to be named) avoid them where the
author has a bound.

**Diverge on the device.** Loops are allowed. A kernel that doesn't terminate hits the
driver's watchdog and loses the device; the host turns that into an error, not a hang. No
termination checking is proposed.

Sketch: the linear-layer op (0), with the dot product as a tail-recursive helper.

```
import std.gpu

data Dims = Dims(u32, u32)                 -- n: outputs per row, k: inputs per row

def dot : &Buf f32 -> &Buf f32 -> u32 -> u32 -> u32 -> f32 ->{Panic, Diverge} f32 =
  \a w x y k acc.
    if k == 0 then acc
    else dot a w (x + 1) (y + 1) (k - 1) (acc + gpu.get a x * gpu.get w y)

kernel linear : &Buf f32 -> &Buf f32 -> &Buf f32 -> Dims -> u32 ->{Panic, Diverge} f32 =
  \a w bias d i. case d of { Dims(n, k) ->
    let row = i / n in
    let col = i % n in
    dot a w (row * k) (col * k) k (gpu.get bias col) }
```

## G3: generating WGSL

`keelc build --target wgsl FILE.kl` writes one `.wgsl` file with an entry point per kernel,
plus a small JSON file that lists each kernel's bindings (buffer element types, parameter record
layout, workgroup size).

Why WGSL text before SPIR-V:

- keelc's back ends already emit text (assembly) and hand it to an external tool;
- `naga` (inside wgpu) validates WGSL and translates it to SPIR-V for Vulkan (the Intel UHD 600),
  MSL for Metal (the Mac) and HLSL, so one back end reaches every GPU energy-timestral uses;
- the output can be read and diffed by hand next to the handwritten `kernels.wgsl`.

A SPIR-V writer is only worth it if WGSL blocks something: a feature naga lacks, or the
validation cost at startup.

Pipeline: kernels leave the shared pipeline after `Mono.hs` and the optimizer, **before**
reference-count insertion. They allocate nothing, so dup/drop has nothing to do, and the
generator works on first-order, monomorphic code with loops. A new `Wgsl.hs` beside
`AArch64.hs`, `X86.hs` and `RiscV.hs`.

Exactness: the GPU doesn't promise the evaluator's results. WGSL allows `exp`, `pow`, `sin`
and `cos` a few ULP of error, and a driver may contract `a * b + c` into an FMA. Tests
compare `run` against the GPU **within a tolerance**, per builtin. This is the one place where
"`run` and the native build print the same output" can't hold, and the test suite must say so.

## G4: launching kernels

**First: the bridge.** Keel emits WGSL and binding metadata (G3), and an existing host (Rust
and wgpu) loads it. For energy-timestral, `src/gpu.rs` keeps creating buffers and dispatching,
`kernels.wgsl` becomes a keelc output, and the parity suite is the test. No GPU runtime goes
into Keel.

**Later: a `GPU` effect.** Host code in Keel performs operations such as

| Operation | Type (sketch) |
|---|---|
| `upload` | `Array f32 => Buf f32` |
| `dispatch` | `(Kernel, Args, u32) => Buf σ` |
| `download` | `Buf f32 => Array f32` |
| `release` | `Buf f32 => Unit` |

`Buf` is **linear**: every buffer is released exactly once, and a released buffer can't be used.
Unhandled, the runtime performs the operations through `wgpu-native`'s C API. Handled, a
handler runs the kernel sequentially in the evaluator, the same pattern as `MMIO` and mock
devices (`examples/uart.kl`). Code without `GPU` in its type never touches the device.
This adds a C dependency to the runtime, which is why it waits for the bridge to prove itself.

## Order and acceptance

| Step | Done when |
|---|---|
| G1 floats | arithmetic, comparisons, conversions and `std.float` on every back end; `run` = `build` exactly; `live=0` |
| G2 kernel subset | the nine ops type-check as kernels; every rule above has a rejecting test; the evaluator runs them through a sequential `dispatch` |
| G3 WGSL | generated kernels pass `naga` validation; each op matches the evaluator within tolerance on the Mac GPU |
| G4a bridge | energy-timestral's `scripts/parity-suite.sh` and `scripts/intel-parity.sh` pass with keelc-generated kernels in place of `kernels.wgsl` |
| G4b `GPU` effect | a Keel host program runs one transformer layer end to end with `live=0` and no leaked `Buf` |

## Open questions

- **Workgroup memory and barriers.** Needed for tiled matrix multiplication, the next
  performance step for the linear layers. Barriers require uniform control flow, which needs
  a uniformity check; and shared memory writes need a race-freedom story stronger than "result
  is the output element".
- **`f16`.** Halves memory traffic on the UHD 600 (4 GB shared), but not every device supports
  it in WGSL (`shader-f16` feature).
- **FMA contraction.** Allow it (faster, small differences) or forbid it (closer to `run`)?
  WGSL can't fully forbid it, so this may only be a tolerance question.
- **Fault reporting.** One atomic word per dispatch, or one per kernel invocation range?
  Does the fault-checking overhead show up in the parity benchmark?
- **Parameter records.** Uniform buffers have alignment rules (16-byte struct alignment);
  the layout of `data` flattened into a uniform must follow them, not keelc's heap layout.
