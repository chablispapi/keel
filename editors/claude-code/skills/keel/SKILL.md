---
name: keel
description: Write, fix or review Keel code (.kl files), a linear, effect-typed language with its own compiler, keelc. Use whenever a task touches a .kl file, the Keel std library, or asks for a program in Keel, even a small one: Keel is not in your training data, and guessing from Haskell or OCaml produces code that almost parses.
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
Keel repository at `${CLAUDE_PLUGIN_ROOT}/../..` (called **the repo** below), and the installed
binary can be older than the repo. If it rejects syntax that the examples use, reinstall it:
`cd ${CLAUDE_PLUGIN_ROOT}/../../ref && cabal install exe:keelc --overwrite-policy=always`. When
you're working on the compiler itself, inside the repo, use
`cd ref && cabal run -v0 exe:keelc -- check FILE.kl` to test the uncommitted compiler.

With the plugin enabled, the language server reports errors in a `.kl` file right after each
edit. Fix them before moving on, the same as for `keelc check`.

## Where to look

- `${CLAUDE_PLUGIN_ROOT}/skills/keel/examples/*.kl`: tested idioms (basics, state threading,
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
  - `Diverge`: any recursion, and calling `map`, `length` and other recursive functions.
  - `IO`: output. `Input`: reading stdin. `Files` and `Net`: files and sockets.
  - User effects: `effect E { op : A => B }`.
  `keelc check` prints the effects a definition actually has, so copy them from the error.
- **Lists:** `Cons(x, box rest)` builds one, and `case xs of { Nil -> … | Cons(x, rest) -> … }`
  takes it apart; `rest` is a `Box (List a)`. Strings are `List u8`, and `'a'` is a `u8`.
- **Printing:** `println "text"`, `printInt n` (no newline), `putc('\n')`, `out(n)` (number plus
  newline). Numbers become text with `string.fromInt n`.
- **Integers:** widths are inferred from context, otherwise `i64`. Convert with `e as u8`, which
  wraps. Use `+%` to wrap, `+|` to saturate, `+?` to get an `Option`.

## Mistakes you will make

Each of these has tripped up someone who had the spec open:

| You write | What happens | Write instead |
|---|---|---|
| a recursive def typed `i64 -> i64` | `EffectMismatch … got i64 →{Diverge, Panic} i64` | the effects from the error: `i64 ->{Panic, Diverge} i64` |
| `f (unbox rest)` forgotten, as in `f rest` | `expected List[…], got Box List[…]` | `f (unbox rest)`: pattern variables of `Box` fields stay boxes |
| `box f x` | `applying a non-function of type Box (…)` | `box (f x)` |
| `g None (Some(4))` | parses as `g (None(Some(4)))`: a constructor takes the parenthesized argument after it, even across a space | `g (None) (Some(4))` |
| `(a, b, c)` | parse error at the second `,`: there are only pairs | `(a, (b, c))` |
| `Cons('+', rest)` in a pattern | parse error: literals only work as the top-level alternatives | `Cons(c, rest) -> if c == '+' then … else …` |
| `map.insert k v m` | type error: no type classes | pass the comparison: `map.insert compareInt k v m`, `string.compare` for strings |
| an unused linear value | `Dropped: x is linear but unused` | consume it (pass it on, or match it to the end) |
| `arena (\u. buildList 10)` | `arena: the result is a pointer` | return a number from it: `arena (\u. length (buildList 10))` |
| a fallthrough nested pattern on `linear data` | `a linear value can't be matched twice` | cover every constructor at each level |
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
  compiler, add it to the table above (this file is
  `${CLAUDE_PLUGIN_ROOT}/skills/keel/SKILL.md`). If it needs an example, add one to
  `examples/` next to it, and register it in the repo's `ref/test/Native.hs` next to the other
  skill examples, so it stays true.
