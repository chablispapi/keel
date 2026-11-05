---
name: keel
description: "Write, fix or review Keel code (.kl files), a linear, effect-typed language with its own compiler, keelc. Use whenever a task touches a .kl file, the Keel std library, or asks for a program in Keel, even a small one: Keel is not in your training data, and guessing from Haskell or OCaml produces code that almost parses."
---

# Writing Keel

Keel is new, and it changes from week to week. Trust `keelc` over your memory and over this
page; when they disagree, the compiler is right (and this page needs fixing).

## The loop: check after every definition

1. Write **one** definition, then run `keelc check FILE.kl`. It takes well under a second and
   gives precise errors with a position (`file:line:col: error [Kind]: …`). Fix those before
   writing the next definition: Keel's errors pile up quickly, and the first one is usually
   the real one.
2. `keelc run FILE.kl` runs the reference evaluator and prints `result: …` (main's value).
3. `keelc build FILE.kl -o OUT && KEEL_STATS=1 ./OUT` runs it natively. The output must be
   the same as `run`, and the stats line must say `live=0` (no leaks). A difference between the
   two is a compiler bug: report it, don't work around it.

`keelc` is the one on `PATH`, which is also what the language server runs. Its source is the
Keel repository, called **the repo** below: this file lives at
`<repo>/editors/claude-code/skills/keel/SKILL.md`, so the repo is four directories up from its
real path. Resolve symlinks first (`realpath`), because this file is often reached through a
link. The installed binary can be older than the repo. A git hook in the repo reinstalls it in
the background (about a minute) after every commit that changes the compiler, so first look at the end of
`<repo>/.git/keelc-install.log`. If an install is running (the directory
`.git/keelc-install.lock` exists next to the log), wait for it. Don't start a second one: the
two would share a build directory. Reinstall it yourself only when the log is missing, is
older than the compiler change, or ends in `install FAILED`:
`cd <repo>/ref && cabal install exe:keelc --overwrite-policy=always`. When
you're working on the compiler itself, inside the repo, use
`cd ref && cabal run -v0 exe:keelc -- check FILE.kl` to test the uncommitted compiler.

In Claude Code with the keel plugin, the language server reports errors in a `.kl` file right
after each edit. Fix them before moving on, the same as for `keelc check`. Other agents don't
get these diagnostics, so run `keelc check` yourself after each edit.

## Where to look

- `examples/*.kl`, next to this file: tested idioms (basics, state threading,
  collections, effects). The repo's test suite compiles and runs them, so they're correct for
  the current compiler. Copy their shapes.
- In the repo, `spec/surface.md`: the full syntax table, the prelude, the std library and the
  modules.
- In the repo, `ref/std/*.kl`: the std library's source, and the most idiomatic Keel there is.
- In the repo, `ref/examples/` and `ref/test/`: more programs. `ref/test/syntax/grammar.kl` has
  every construct.
- In the repo, `spec/core.md`: what linearity, effects and references mean, when an error
  message isn't enough.

## Shape of a program

```
import std.string                         -- imports first; std.map, std.array, std.file, std.loop

data Shape = Circle(i64) | Rect(i64, i64) -- `linear data` for resources that can't be copied

def area : Shape ->{Panic} i64 =          -- every top-level def has a type
  \s. case s of { Circle(r) -> 3 * r * r | Rect(w, h) -> w * h }

main = printInt (area (Rect(3, 4))); putc('\n'); 0
```

- **Functions:** `\x y. e` is a λ, `f x y` an application, `let x = e in e` a binding,
  `let (a, b) = p in e` takes a pair apart, and `e1; e2` is sequencing. `if` always has an `else`.
- **Effects:** they go in the arrow, `a ->{IO, Panic, Diverge} b`. The ones you'll use most:
  - `Panic`: checked arithmetic (`+ - *` panic on overflow), `/`, array indexing.
  - `Diverge`: recursion that isn't on a part of a parameter (a variable a `case` bound from
    it), such as counting an integer down or reading until end of input. Recursion on a list
    or tree (`length (unbox rest)`), and calling `map`, `length` or `foldl`, needs none.
  - `IO`: output. `Input`: reading stdin. `Files` and `Net`: files and sockets.
  - `Alloc`: building or holding a heap block. Every arrow allows it without saying so;
    `->{!Alloc}` forbids it, for code that must not touch the allocator. On RISC-V firmware,
    `def interrupt : usize ->{MMIO, !Alloc} Unit` is the interrupt handler (`test/firmware/interrupt.kl`).
  - `Shared`: cells, the only mutable state outside functions. `cell n : u32 = 0` or
    `cell buf : [u8; 64]`, read with `get(n)` / `getAt(buf, i)`, written with `set(n, v)` /
    `setAt(buf, i, v)` (`test/cells/cells.kl`). They don't allocate, so an interrupt
    handler and `main` can share them. For messages from the handler to `main`, use a
    queue: `queue rx : [Rx; 16]`, `post(rx, Byte(b))` in the handler and
    `case receive(rx) of { Byte(b) -> … | Lost(n) -> … | Empty -> … }` in `main`
    (`test/cells/queue.kl`).
  - User effects: `effect E { op : A => B }`.
  `keelc check` prints the effects a definition actually has, so copy them from the error.
- **Lists:** `Cons(x, box rest)` builds one, and `case xs of { Nil -> … | Cons(x, rest) -> … }`
  takes it apart; `rest` is a `Box (List a)`. Strings are `List u8`, and `'a'` is a `u8`.
- **Printing:** `println "text"`, `printInt n` (no newline), `putc('\n')`, `out(n)` (number plus
  newline). Numbers become text with `string.fromInt n`.
- **Integers:** widths are inferred from context, otherwise `i64`. Convert with `e as u8`, which
  wraps. Use `+%` to wrap, `+|` to saturate, `+?` to get an `Option`.
- **Floats:** `f64` only, with literals `1.5`, `2.0`, `1e-9`. `+ - * /` and comparisons never
  panic (IEEE: `inf`, `NaN`). Convert with `n as f64` and `x as i64` (truncates, saturates).
  `import std.float` for `float.sqrt`, `abs`, `min`, `max`, `isNaN`, and on hosted targets
  `exp`, `log`, `pow`, `sin`, `cos`, `floor`. Print with `string.fromFloat x`. Not on RV32.

## Mistakes you will make

Each of these has tripped up someone who had the spec open:

| You write | What happens | Write instead |
|---|---|---|
| a def recursing on an integer (`f (n - 1)`) or a rebuilt value, typed `i64 -> i64` | `EffectMismatch … got i64 →{Diverge, Panic} i64` | the effects from the error: `i64 ->{Panic, Diverge} i64`. Recursion on a `case`-bound part of a parameter needs no `Diverge` |
| `f (unbox rest)` forgotten, as in `f rest` | `expected List[…], got Box List[…]` | `f (unbox rest)`: pattern variables of `Box` fields stay boxes |
| `box f x` | `applying a non-function of type Box (…)` | `box (f x)` |
| `g None (Some(4))` | parses as `g (None(Some(4)))`: a constructor takes the parenthesized argument after it, even across a space | `g (None) (Some(4))` |
| `(a, b, c)` | parse error at the second `,`: there are only pairs | `(a, (b, c))` |
| `Cons('+', rest)` in a pattern | parse error: literals only work as the top-level alternatives | `Cons(c, rest) -> if c == '+' then … else …` |
| `map.insert k v m` | type error: no type classes | pass the comparison: `map.insert compareInt k v m`, `string.compare` for strings |
| an unused linear value | `Dropped: x is linear but unused` | consume it (pass it on, or match it to the end) |
| `arena (\u. buildList 10)` | `arena: the result is a pointer` | return a number from it: `arena (\u. length (buildList 10))` |
| a fallthrough nested pattern on `linear data` | `a linear value can't be matched twice` | cover every constructor at each level |
| `if c then a else b; e` meaning `else (b; e)` | `;` binds looser than `if`, so `e` runs after either branch; often `expected Unit, got …` on the `then` branch | parenthesize the branch: `else (b; e)` |
| `bitdata R : u8 { a @ 0, b @ 5 }` | parse error at the `,` | separate fields with `;`: `{ a @ 0 ; b @ 5 }` |
| `!Alloc` on every arrow, as in `i64 ->{!Alloc} i64 ->{!Alloc} i64` | `only its last parameter's arrow can be !Alloc` | only the last: `i64 -> i64 ->{!Alloc} i64` |
| `x + 1` or `x * 2` with `x : f64` | `expected f64, got an integer` | `x + 1.0`: an integer literal is never a float |
| `x % 2.0`, `x +% y` or `x land y` on `f64` | `f64 has only + - * / and comparisons` | `x - float.floor (x / 2.0) * 2.0` for a remainder (hosted) |
| `printInt x` or `out(x)` with `x : f64` | `expected i64, got f64` | `println (string.fromFloat x)`, or `out(x as i64)` |
| `n + 1` with `cell n : u32` | `cell n is read with get(n) and written with set(n, v)` | `get(n) + 1`: a cell isn't a value |
| `cell total : i64` | `a cell holds an integer of up to 32 bits, or a usize` | `u32`, `i32` or `usize` |
| `def interrupt` doing `out(…)` when `main` never prints | `def interrupt has effects {IO} that main doesn't` | `main` must have the handler's effects: give it the operation too, or drop it from the handler |
| `case receive(rx) of { Byte(b) -> … \| _ -> … }` | `receive(rx): _ would hide a message` | an alternative for each message, plus `Lost(n)` and `Empty` |
| `post(rx, m)` with `m` a variable, or `post` in a function `main` calls | `m is a Rx constructor written out there`, or `only def interrupt, and what it calls, posts to a queue` | `post(rx, Byte(b))`, in the handler's side only |
| a `forall 'e` function that handles `Log` around a `'e` argument, called with a `Log`-performing function | `quiet handles Log around code with effect 'e, and here 'e has Log` | handle the argument's `Log` before passing it: `quiet (\u. handle … with Log { … })` |
| `write8 p` with `p` a pair variable, in a `!Alloc` function | `… is !Alloc, but it uses p, which holds a heap block` | write the pair at the call, `write8(a, v)`: then the two words go in registers |
| `p.x` on data | `can't tell the type before .x (got P); add a type annotation`. Ignore the hint: `.obs` is only for codata, and data has no field access | match: `case p of { P(x, _) -> x }` |

## Idioms

- **Nested patterns** are fine and preferred: `case xs of { Cons(a, Cons(b, _)) -> … | _ -> … }`
  and `case (a, b) of { (Some(x), Some(y)) -> … | _ -> … }`. A pattern inside a `Box` field
  looks through the box, and a `case` on a boxed value matches its contents.
- **State is threaded:** a parser takes the input and returns `(result, rest)`. A counter or an
  environment is an extra parameter, returned with the result. Write this out; don't reach for
  a monad.
- **Loops are tail-recursive helpers** with an accumulator (`sumTo i acc`), and they run in
  constant stack. A `var x = e in …` with `x := e` is a local mutable variable, and a `&mut x`
  parameter lets a callee update it.
- **Collections:** `std.map` for lookup tables, `std.array` for indexing (`array.push`,
  `array.get`, `array.set`). Arrays are values, and threading one through updates updates it in
  place. After `import std.array`, write `array.length`: a plain `length` is ambiguous with
  the prelude's.
- **Interfaces** are codata: `codata Order a { lt : a -> a -> Bool }`, built with `cocase` and
  used as `o.lt x y`.
- **Devices and mocks** are effects. Code performs `sample(n)`, and
  `handle e with Sensor { sample i -> … }` decides what that means; the clause's value is the
  operation's result.
- **Text building:** consing onto an accumulator and reversing at the end is cheaper than
  `append` in a loop. `string.join`, `string.split` and `string.lines` handle the common cases.

## When you're done

- `keelc check` is clean, and `run` and the native build print the same output with `live=0`.
- If you learned something that would have saved you time, and it's true of the current
  compiler, add it to the table above (in this file, at its real path in the repo). If it needs
  an example, add one to
  `examples/` next to it, and register it in the repo's `ref/test/Native.hs` next to the other
  skill examples, so it stays true.
