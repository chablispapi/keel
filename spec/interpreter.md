# A self-hosted interpreter and REPL

Status: proposed 2026-11-13, revised 2026-11-13 after review.

## Goal

A second implementation of Keel's semantics, written in Keel, in `ref/selfhost/`. It has two
phases, and the first is the gate for the second:

- **Phase A, a batch driver** that reproduces `keelc run` exactly: the same stdout, the same
  `result: <value>` line, the same `panic:` messages and the same written files. It is compared
  with the reference evaluator on the whole corpus, as `parser.kl` and `checker.kl` already are.
  This is the correctness oracle.
- **Phase B, a REPL** on the same evaluator, shaped like GHCi: a prompt, expressions checked and
  evaluated in the session's context, declarations that accumulate, `let` bindings, `:load` and
  `:type`.

Both drivers share one `eval.kl`. They differ only in how they handle the device effects
(below), so there is no second semantics.

## Why this is mostly assembly

| Piece | Status | Reuse |
|---|---|---|
| lexer, parser | `lexer.kl`, `parser.kl` | as-is; the parser already turns nested patterns into flat cases and literal patterns into `if`/`EPrim` (`parser.kl:707`), so the evaluator never sees patterns |
| module loading, program-wide name resolution | inside `check.kl` (230 lines) | extract into `load.kl` and share |
| inference (literal widths, constructor type arguments), `var`/`&mut` elaboration, bitdata/cell/queue lowering | `checker.kl` (`inferAll`, `elabDecl`, `elabMain`) | add one entry point that returns the elaborated program; **its output shape is unverified, see M0** |
| semantics to port | `ref/src/Keel/Eval.hs` (455 lines) | the authority; port case by case |
| test pattern | `selfhostChecks`, `selfhostCheckChecks` in `ref/test/Native.hs` | copy the shape |

After `checker.kl` has run, the term should be close to core. `var`/`:=` become `let`s, `&x`
becomes a call that returns a pair, bitdata becomes shifts and ors, `get`/`set`/`post`/`receive`
become `%cellLoad`/`%cellStore`, and literal patterns become `if`s. What is left should be
exactly what `Eval.hs` handles. M0 checks that this is true.

## Files

| File | Phase | Role |
|---|---|---|
| `ref/selfhost/load.kl` (new, ~180 lines) | A | everything in `check.kl` above the verdict: `Result`, `visit`, `Scope`, `Res`, `plain`/`name`/`term`/`decl`, `baseName`, `programOf`, plus `resolveTerm` for prompt input |
| `ref/selfhost/check.kl` | A | becomes thin: `programOf`, then `checker.verdict` (done) |
| `ref/selfhost/sexp.kl`, `core.kl` | A | S-expression printers (from `parse.kl`) and the core dump (done) |
| `ref/selfhost/checker.kl` | A | `program` returns the elaborated program and its entry's type and effects; real cell slot numbering |
| `ref/selfhost/eval.kl` (new, ~1000–1400 lines) | A | value model, evaluator, `show` |
| `ref/selfhost/run.kl` (new, ~250 lines) | A | batch driver, plus the mock device handler (files, loopback net) ported from `Eval.hs`'s `machine`/`network` |
| `ref/selfhost/repl.kl` (new, ~300 lines) | B | prompt loop, session state, `:` commands |
| `ref/test/Native.hs` | A, B | `selfhostEvalChecks` (batch differential), `selfhostReplChecks` (golden scripts) |

## Evaluation model

```
data Value = VUnit | VInt(Ty, i64) | VFloat(f64) | VBool(Bool)
           | VCon(List u8, List Value) | VBox(Box Value) | VPair(Box Value, Box Value)
           | VClo(Box Env, List u8, Term)              -- λ and λ° alike
           | VCodata(Box Env, List (List u8, Term))    -- branches
           | VArray(Array Value)                       -- the builtin Array: O(1) get/set
type Env = List (List u8, Value)                       -- locals only; closures share it
type Globals = map.Map (List u8) Global                -- never captured by a closure
```

- **Globals are a separate table, not part of `Env`.** `Eval.hs` makes the top-level definitions
  a lazy knot (`globals = M.fromList [(f, eval … globals e)]`, `Eval.hs:116`). Keel is strict and
  reference-counted with no mutation, so it cannot build a cycle, and a closure cannot capture an
  `Env` that contains itself. Instead, `eval` takes `Globals` as a parameter. A variable is
  looked up in `Env` first, then in `Globals`. A top-level lambda is stored as its code. A
  top-level value that is not a lambda is evaluated once, in dependency order, and cached. This
  is allowed because top-level bodies are effect-free, which the checker enforces. Because
  globals are never in a local `Env`, local environments stay small, so an association list is
  fine. A REPL `def` is a map insert.
- Every recursive `Value` field goes through `Box` or a function. `List` alone is not enough:
  `Cons` holds its element unboxed, so `VClo(List (…, Value), …)` is `InfiniteSize`. Hence
  `Box Env`.
- **Devices are effects, not state.** eval.kl *performs* the builtin operations it does not
  model: `out`, `putc`, `getc`, `openFile`, `createFile`, `appendFile`, `readByte`,
  `writeBytes`, `closeFile`, `tcpListen`/`tcpAccept`/`tcpConnect`, `sock*`, `pollWait` and
  `clockMs`. A handler can
  catch these as it would any other operation (`Eval.hs`'s `machine` comment).
  - `run.kl` wraps the evaluator in a `handle` that mocks them exactly as `Eval.hs`'s
    `machine`/`network` do. stdin is the rest of the batch input. Readable files are those
    of `Native.hs`'s `machineFor`. Written files are kept in memory. The network is the
    simulated loopback, starting at fd 3 and port 49152.
  - `repl.kl` leaves them unhandled, so the REPL does real I/O.

  The only state eval.kl threads itself is the cell array (`Array u64`, O(1) load and store).
  Output is written as it happens, so a panic needs no flush step. `eval` returns
  `Val(Value, Cells) | Bad(List u8, Cells)`. `Bad` is a
  panic of the interpreted program, and only interpreter bugs panic the interpreter itself.
- **Integers follow `Eval.hs`'s shape (`Eval.hs:364`)**: compute the exact result, then
  range-check it against the width. Values are stored as their bit pattern in an `i64`.
  - For widths up to i64, compute with the optional operators (`+?`, `-?`, `*?`). For a result
    that fits, check it against `intRange(t)`. Then apply Checked, Wrap, Saturate or Optional
    exactly as `Eval.hs` does. `None` from the 64-bit operation means the result is out of range.
  - **u64** is the only width that needs its own path: unsigned compare, `show` and division.
    `as u64` / `as i64` round-trip bit patterns because `as` is modulo.
  - **`usize` is u64**, as `runProgramAt 64` resolves it (`Syntax.resolveWord`).
  - Shift counts are clamped to 64, and a shift of 64 is a special case because the native
    shift would not give `Eval.hs`'s Integer result. `>>` is arithmetic on signed widths and
    logical on unsigned ones.
- **Native stack: plain recursion (decided in M0).** `eval` is an ordinary recursive function,
  with no trampoline and no CEK machine. keelc compiles tail calls as jumps, so if `eval` calls
  itself in tail position for an application's body, a `let` body, the branches of `if` and
  `case`, and the second half of `;`, an interpreted tail call takes no native stack. **Keep
  those calls in tail position:** no wrapping or post-processing of their result. Non-tail
  interpreted calls cost about 2.5 native frames each (see M0 results).

### Semantics to port, in order

1. Call by value, strictly left to right: `App` (function, then argument), `Prim`, `Pair`,
   `Con` arguments, array builtins. Output order depends on this.
2. `Var` (locals, then globals), literals, `If`, `Let`, `Seq`, `Box`/`Unbox`,
   `Pair`/`LetPair`, `Lam`/`App`, `Con`, `Case` (in source order, then `_`). `TyApp`/`At` are
   erased.
3. `Prim`: as described above. Division by zero gives `division by zero`. The overflow panic
   text is exactly `arithmetic overflow: a + b in i64`.
4. `Convert`: wraps modulo, per target width.
5. Floats: literals, `+ - * /`, comparisons (`FGe` for `>=`), and conversions both ways (`as i64`
   saturates, NaN gives 0). Also `floatSqrt`/`ToBits`/`FromBits`/`Exp`/`Log`/`Sin`/`Cos`/`Pow`/
   `Floor`.
6. Arrays and `arena` (apply its argument to `()`). Out of bounds gives
   `array index out of bounds`.
7. `Perform`/`Handle`: use the innermost handler that has the operation. The clause runs with
   the **outer** handlers only, in the env at the handle site plus its one parameter. Its value
   is the operation's result (tail-resumptive, no continuation). If no interpreted handler has
   the operation:
   - `%cellLoad`/`%cellStore` use the cell array;
   - MMIO and Hart give `unhandled operation <op> (no device memory in the evaluator)`;
   - anything else is performed for real, which is the device effects above.
8. `Cocase`/`Proj`: the branch runs in the env at the cocase site, with the handlers at the
   projection site.
9. `show`:
   - `()`; `true`/`false`;
   - integers in decimal by signedness. u64 prints unsigned from its bit pattern, and
     `std.string.fromInt` is i64-only, so write a u64 printer in the style of `digitsOnto`;
   - floats as `0x` plus the lowercase hex of `floatToBits`;
   - `C` and `C(a, b)`; `box v`; `(a, b)`; `[a, b]`; `<closure>`; `<codata>`.

## The REPL (Phase B)

### Session model

```
data Session = Session(
  List Decl,     -- def/data/cell/queue/effect/codata/bitdata entered at the prompt, and lets
  Globals,       -- evaluated globals: the loaded file's, then the prompt's
  Res,           -- resolver from :load, or the prelude alone
  Array u64)     -- cells, carried between commands
```

Every command is checked by running the front end again over the whole accumulated program
(`buildSig` → `inferAll` → `checkRefs` → `elabMain` → `checkCore`). This is the only way to
keep types, effects and linearity correct. M0 measures the cost per prompt, because the prelude
and the loaded file are re-checked on every line.

- **An expression is a synthetic `main`.** Prompt text becomes `Module(imps, decls, Some expr)`.
  `load.kl`'s `term` resolves it with the session's `Res`, `checker.program` infers its type and
  effects, and the evaluator runs the elaborated term. Errors, effect rules and linearity are
  therefore exactly those of `keelc run`, with nothing to keep in sync.
- **`let x = e` is a def.** Infer `e`. Require a `Free` type that is not linear (`isLin`) and an
  empty effect row; otherwise refuse with a message pointing at `def`. Then append
  `def x : T = e` to the session and print `x : T`. A global value is evaluated once, so this has
  GHCi's evaluate-once meaning and needs no checker hook for seeded locals. A name that is
  already defined is an error, as for `def`; use `:clear`.
- **`def`, `data`, `cell`, `queue`, `effect`, `codata` and `bitdata`** append to the session.
  Only new names are accepted. Redefinition is an error because old closures and cell offsets
  must stay valid. `:load` is the reset.
- **Failures never commit.** Prepare on a copy, print the checker's `error [Kind]: …` (or
  `unsupported: …`), and leave the session unchanged. A bad line does not end the session.
- **State persists on purpose.** Cell words carry over. Device effects are real, so open files
  stay open, and the interpreted program's `getc` reads the terminal after the current line,
  as in GHCi. `:load` resets the cells.
- **`def interrupt`** is allowed but skipped by the REPL's `checkCore`. Otherwise the
  `interruptErr` rule would force `IO` onto every prompt expression. The interrupt runs
  nowhere, as in `keelc run`.
- A **linear result** is a `Dropped` error. A REPL can run code more than once, and silently
  duplicating a linear value would break the property the language exists for.

### Commands

| Command | Behaviour |
|---|---|
| `EXPR` | check and evaluate as `main`, then print `show v` (no `result: ` prefix); effects run for real |
| `let x = e` | monomorphic value binding, stored as a def; prints `x : T` |
| `def …`, `data …`, `cell …`, … | append to the session; print `ok` or the checker's error |
| `:load PATH` / `:r` | load modules, resolve names, print the verdict, and reset decls, globals and cells; `:r` reloads the last path |
| `:type EXPR` (`:t`) | inference only, printed with `showTy` + `showRow`; no evaluation |
| `:clear` | drop prompt declarations, keep the loaded file |
| `:{ … :}` | multi-line input, so `data`/`def` declarations can span lines |
| `:help`, `:quit`/`:q`, EOF | help; exit 0 |

The prompt is `keel> ` and the continuation prompt is `     | `. Both are written through the
runtime before each read so that golden outputs are deterministic.

Not in the first version: `:info` (it needs the signature accessors exported, plus `sigCells`),
`:check` (`keelc check` already does it) and `:main`. Add them when someone asks.

### Checker hooks

1. `program` returns the elaborated declarations plus the entry's `(Ty, effects)`. `verdict`
   becomes its formatter. (Phase A)
2. Number cell slots for real, replacing the stub at `checker.kl:1156`. (Phase A)
3. A `repl : Bool` argument that skips `interruptErr`. (Phase B)

## Milestones

Each one ends green on its slice of the corpus.

| # | Deliverable | Gate |
|---|---|---|
| M0 | **Spikes, no evaluator yet.** (a) The checker contract: `checker.program` and a dump of its elaborated core for `examples/fact.kl`, one numeric test, one cells test and one handler test, diffed by hand against `Elab.elaborate`. Literal widths must be solved in the term, not left as type-variable names (`checker.kl:858`), and `f64` literals must not be `unsupported` (`checker.kl:863`). (b) Stack: the native stack limit of a keelc binary, the frame size of a toy `eval`, and the deepest non-tail recursion in the corpus. Decide trampoline or CEK. (c) Costs: re-check time for prelude plus the largest corpus file; `keelc build` time for a program linking parser, checker and a stub eval. | a short written decision in this file; `load.kl` extracted and `selfhostCheckChecks` unchanged |
| M1 | `eval.kl` with globals, data/case/pairs/codata, all integer widths and modes, `as`, bits; `run.kl` | `test/syntax/*`, `test/numeric/int*`, `test/memory/narrow-print.kl` |
| M2 | handlers, `out`/`putc`/`getc` through the mock, panics, cells and queues with real offsets | `test/cells/*` |
| M3 | floats, arrays, builtins, float hex `show` | `test/numeric/float*.kl`, `test/std/{array,vector}.kl`, `test/memory/array32*.kl` |
| M4 | files in the mock (`machineFor`'s files, in-memory writes) | `examples/words.kl`, `test/std/file*` |
| M5 | loopback net in the mock: listeners, sockets, 64 KiB buffers, `poll` readiness, `pollWait`/`clockMs`, fd and port allocation, exact failure strings | `test/net/*`; **Phase A done** |
| M6 | REPL: `EXPR`, `let`, decls, error recovery, cell persistence, `:load`/`:r`, `:type`, `:clear`, `:{ :}`, `:help`, `:quit`, EOF | golden scripts in `ref/test/repl/`, including `1 + 2` → `3`, `let x = 2` then `x * 3` → `6`, `cell c : u32 = 0`, `set(c, 41)`, `get(c) + 1` → `42` |
| M7 | performance: environment lookup, closure size, caching prelude globals | whole-corpus time plus session startup, reported like `checker.kl`'s measurement block |

## M0 results

**(a) The checker's output, 2026-11-17: done.** `checker.program` returns
`Core(decls, main, type, effects) | Rejected(msg)`, and `verdict` formats it. `selfhost/core.kl`
prints the core as S-expressions (`sexp.kl`, split out of `parse.kl`). It was compared with
keelc's `elaborate (inferProgram p)` on every file in the corpus. All 76 accepted files print the
same tree, and keelc rejects the 78 files selfhost rejects. The comparison ignores four
differences of notation, which the evaluator handles by name:

- keelc's `Perform op e` is `(app op e)`. An application of a name that is neither local nor
  global, and is an operation, performs it.
- keelc's `ArrayPrim`/`FloatPrim` are the builtin's name applied, with an array operation's
  head as `(tyapp arrayGet (a))`. `arena` is `(app arena f)`.
- A `tyapp` carries its effect arguments as `(-> Unit (row) Unit)` types. They are erased.
- keelc marks one-shot lambdas `\o`; selfhost does not. They evaluate the same.

Getting there took four checker changes:

- **The prelude is inferred** with the program. It used to be only in the signature, so its
  literals had no width (`printU64`'s `10` must be u64). keelc's meta numbering now matches too
  (`?58`, not `?1`).
- **Cell slots are numbered** as `Syntax.cellSlots`. Queues expand in place into their
  `head tail lost seen tag f0…` cells, and these appear as `DCell`s in the core, so the
  evaluator computes the initial words as `cellInits` does.
- **`post` uses each cell's own slot.** A full queue now increments `lost` as keelc does (it
  used to write `head`).
- **`>=` and `<=` on f64** become core `>=` (keelc's `FGe`, IEEE semantics on NaN) through
  `notLess`, as in `Keel.Infer`. On integers they stay `if a < b then false else true`.

The two traps listed for M0(a) were not real. Literal widths were already solved by
`finish`/`zonkTerm`. The `f64`-suffix `unsupported` is unreachable in the corpus, because float
literals are `EFloat`.

**(b) Stack, 2026-11-17: plain recursion.**

- On the host targets, a native Keel program runs on the OS main-thread stack (`AArch64.hs:1554`,
  `X86.hs:1094`). It honours `ulimit -s`, has no overflow check, and dies with SIGSEGV (exit 139)
  on overflow. RISC-V uses a fixed `.bss` stack: 8 MiB on `Virt`, 64 KiB on `Pico2`
  (`RiscV.hs:70`). Tail calls are jumps (`AArch64.hs:692`).
- A toy evaluator shaped like `eval.kl` (parser `Term`s, an association-list env, globals in a
  map, an `Out` result threading a word) was measured against native code on
  `down n = 1 + down (n - 1)`. Native code reaches depth ≈260k in 8 MiB (≈32 B per frame), the
  toy ≈104k (≈80 B per interpreted call). An interpreted tail loop (`sumTo 3000000 0`) runs in
  64 KiB.
- Every corpus program that builds natively (66, with the batch differential's inputs) runs in
  64 KiB, so even a 10× interpreter overhead fits in the default 8 MiB. The deep case is outside
  the corpus: `core.kl` checking its own 4.3k lines natively needs 2–4 MiB, so interpreting that
  would need about 10–30 MiB. Document `ulimit -s 65520` (the macOS hard limit) for it rather
  than build a CEK machine.

**(c) Costs, 2026-11-17.** Medians of 3 runs on the M-series host:

| What | Time |
|---|---|
| `keelc check selfhost/core.kl` (parser + checker + load + sexp, ≈4.3k lines) | 10.5 s |
| `keelc build selfhost/core.kl` / `check.kl` | 16.3 s / 14.8 s |
| native `core.kl` on `examples/fact.kl` (prelude + program: infer, elaborate, check) | 0.02 s |
| native `core.kl` on itself | 0.68 s |

Re-checking the session on every REPL line is therefore cheap, unless the loaded file is the
size of the checker. The cost is in the build. `run.kl` and `repl.kl` will each take about
20 s+ to build, and `cabal test` builds both.


**`selfhostEvalChecks` (batch differential).** Same shape as `selfhostCheckChecks`, and wired
into the same `sequence` in `Native.hs`:

1. Build `selfhost/run.kl` natively once, and print how long the build took.
2. Corpus: the same `klFiles ["examples","std","test","selfhost"]` walk. Skip files keelc
   rejects; `selfhostCheckChecks` already compares those.
3. Expected: `loadModules f >>= inferProgram >>= compile`, then
   `runProgramAt 64 (machineFor f)`. Render `output ++ "result: " ++ show v` or
   `output ++ "panic: " ++ msg`, followed by the written files in a fixed format: one
   `file <path>` line, then the contents, for each file in path order.
4. Actual: `printf '%s\n%s' f (exampleInput f) | run-exe`. run.kl's mock prints the written
   files in the same format after the result line. Compare stdout only; nothing touches the
   disk.
5. `unsupported: …` from the interpreter counts as a skip. Print
   `selfhost evaluator: N agree, M unsupported`, and list any disagreement with its diff. Fail
   loudly on a crash or a timeout (use a per-file timeout).

**`selfhostReplChecks` (golden sessions).** Build `repl.kl` once. For each
`ref/test/repl/NAME.in`, feed it with a timeout and compare stdout with `NAME.out` exactly,
prompts included. One script per feature:
- expression typing and printing;
- `let`, and a `let` that redefines a name (refused);
- `def`/`data` declarations;
- cell persistence;
- `:t` on a polymorphic def;
- `:load` then a call into the file;
- a rejected expression followed by a good one;
- `:{ :}`;
- EOF exit.

## Limits to document in `:help` and the file header

- No line editing or history: Keel has no terminal control, so arrow keys arrive as bytes.
  `rlwrap keel` works from outside.
- No Ctrl-C: a divergent expression hangs the session.
- No `:!`, `:cd` or `:set`; no redefinition (use `:load` or `:clear`); no polymorphism at the
  prompt (use `def`).
- Every expression obeys `main`'s rules: linear results are `Dropped`, and `let` is monomorphic
  and effect-free.

## Known traps

- **Cell offsets are not numbered.** `checker.kl:1156` says "every offset is 0: the checker
  never reads one." The interpreter does read them. Port `Syntax.cellSlots`/`queueCells`/
  `cellInits` into `checker.kl`'s `xsOf`, expanding queues into their 4 + 1 + k cell arrays
  first, in declaration order. Verdicts must not change; the checker differential proves it.
- **u64** is the only width whose values do not fit in `i64`. Store bit patterns and dispatch on
  signedness per operation, including `show` and `<`.
- **Float parity** must be exact: `show` prints the IEEE bits. Check in M0 that keelc's native
  `floatExp`/`Sin`/`Cos`/`Pow`/`Log` call the system libm, as `Eval.hs`'s FFI does. If they are
  inline implementations, bits can differ. Do not format floats.
- **Panic text is part of the interface.** Copy the strings from `Eval.hs` verbatim, including
  `in i64`.
- **stdin is the only channel** (Keel has no argv). The batch protocol is therefore `path\nrest`.
- **Build time.** `keelc check checker.kl` takes 14.8 s and grows faster than the code does.
  repl.kl links parser, checker and eval (about 5k lines), and `cabal test` builds it on every
  run. M0 measures this, and the harness prints it.
- **Performance.** The interpreter runs the prelude from source (`selfhost/prelude.kl`) for every
  program, whereas `keelc run` runs the compiled prelude. Publish the corpus time.

## Definition of done

- `selfhostEvalChecks`: every runnable file in the corpus agrees with `keelc run`, with no
  `unsupported` skips left. `selfhostReplChecks`: all golden scripts pass.
- `keelc check selfhost/{eval,run,repl,load}.kl` is clean, and `keelc build` of each prints
  `live=0`.
- `selfhostCheckChecks` still prints the same agree/unsupported counts after the `load.kl`
  extraction and the cell-numbering change.
- Docs updated:
  - `AGENTS.md`: the "Two parsers" bullet becomes parser, checker and interpreter;
  - `README.md`'s self-hosting line;
  - `notes.md` M5's "Not yet" list.

  No change to `spec/surface.md` or `spec/core.md`: the language's semantics do not change.
