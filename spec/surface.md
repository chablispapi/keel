# Keel surface syntax

The language you write in `.kl` files. `keelc` parses it (`ref/src/Keel/Parser.hs`), infers what
Keel Core needs explicitly (`ref/src/Keel/Infer.hs`), then runs the core pipeline of
`spec/core.md`. Examples are in `ref/examples/`.

```
keelc new NAME                 create a project: NAME/keel.project, NAME/src/main.kl
keelc check [FILE.kl]          type-check; print main's type and effects
keelc run   [FILE.kl]          run with the reference evaluator
keelc asm   [FILE.kl]          print the ARM64 assembly
keelc build [FILE.kl] [-o OUT] [--target native|riscv64]
                               native executable (via the system cc), or a freestanding
                               RISC-V image for QEMU's virt board
keelc qemu  [FILE.kl]          build for RISC-V and boot it in QEMU
```

Without a file, the commands use the project in the current directory (see "Projects and
modules" below).

The RISC-V target needs Homebrew's `llvm`, `lld` and `qemu`. It is freestanding: no operating
system and no C library. Output goes through the board's 16550 UART, and the program exits
through its test device (status 101 on a panic).

## Programs

A file is a list of declarations followed by `main = expression`. Comments are `-- …` and `{- … -}`.

```
[linear] data List a = Nil | Cons(a, Box (List a))
codata Ord a { lt : a -> a -> Bool }
bitdata LineStatus : u8 { thr_empty @ 5 ; parity @ 1..2 }
effect MMIO { read : i64 => i64 ; write : W => Unit }
def name : type = expression        -- top-level definitions need a type
main = expression
```

Capitalized names are types, constructors and effect labels; lowercase names are variables,
type variables, operations and observations.

## Types

| Syntax | Meaning |
|---|---|
| `i8` … `i64`, `u8` … `u64`, `Bool`, `Unit` | base types |
| `a -> b`, `a ->{Panic, 'e} b` | function, with effects |
| `a -o b`, `a -o{IO} b` | linear (one-shot) function |
| `&a -> b`, `&mut a -> b` | reference parameters (only as a parameter) |
| `List a`, `Box a`, `(a, b)` | data / codata types, boxes, pairs |
| `forall a (b : Free) 'e. type` | polymorphic definition type; kind defaults to `Lin` |

Arrows associate to the right. Effect variables start with `'`.

## Expressions

| Syntax | Core |
|---|---|
| `\x y. e`, `\(x : i64). e`, `\&mut x. e` | λ (parameter types are inferred when possible) |
| `f x y`, `f(&mut x)`, `f &x` | application, borrows |
| `let x = e in e`, `let (x, y) = e in e` | let, pair destructuring |
| `var x = e in e`, `x := e`, `e; e` | mutable local, assignment, sequencing |
| `if c then a else b` | conditional |
| `case e of { Nil -> a \| Cons(x, rest) -> b }` | pattern matching |
| `cocase Ord { lt -> \p q. p < q }`, `e.lt` | codata value, observation |
| `handle e with MMIO { read a -> e \| write w -> e }` | handler |
| `read8(4)`, `out(x)`, `putc(c)` | performing an operation (`out` prints a number and a newline, `putc` one byte) |
| `Cons(1, box Nil)`, `box e`, `unbox e`, `(a, b)` | constructors, boxes, pairs |
| `42`, `250u8`, `0x1000_0000`, `-5`, `true`, `()` | literals (width inferred unless suffixed; `_` separates digits) |
| `"Hi!\n"` | a `List u8` of the string's UTF-8 bytes (Haskell-style escapes) |
| `/`, `%` | division truncating toward zero, remainder; panic on division by zero and `min / -1` |
| `x land y`, `lor`, `lxor`, `lsl`, `lsr` | bitwise and, or, xor, shifts (logical for unsigned types, arithmetic for signed) |
| `e as u8` | wrapping conversion between integer types |
| `s.thr_empty`, `s.raw`, `LineStatus(x)`, `LineStatus { thr_empty = 1 }` | bitdata field, raw value, from raw, from fields |
| `+ - *`, `+% -% *%`, `+\| -\| *\|`, `+? -? *?` | checked, wrapping, saturating, Option arithmetic |
| `==`, `<` | comparisons |
| `f[i64]`, `Nil[i64]` | explicit type arguments (usually inferred) |

Precedence, loosest first: `;`, then `λ` / `let` / `var` / `if` / `handle` / `:=` (their bodies
extend as far as possible), then `==` `<`, then `+ -` (all variants), then `*` and the bitwise
operators, then `as`, then application, then `.obs` and `[types]`. A `-` directly before a number at the start of an
operand is a negative literal; `n -1` still means `n - 1`.

## Projects and modules

**Modules.** One file is one module. A file starts with its imports:

```
import util               -- util.kl
import drivers.console    -- drivers/console.kl
```

Paths are relative to the entry file's directory, and imports load transitively. Imported
declarations are visible by their plain names. A declaration marked `private` is visible only in
its own file: private names are renamed per module, so two modules can each have a
`private def helper`. Only the entry file may define `main`. The loader reports import cycles
(`import cycle: a → b → a`), missing modules (with the position of the `import`), and a public
name declared by two modules (naming both files). Errors anywhere name the right file.

There are no namespaces yet: public names share one scope, so they must be unique across a
program. Qualified names (`console.greet`) need a syntax that doesn't collide with observations
(`e.obs`).

**Projects.** `keelc new NAME` creates a directory with a manifest, a `src/main.kl` and a
`.gitignore`. The manifest, `keel.project`, has `key = value` lines:

```
name = modules           # output: build/modules
main = src/main.kl       # the entry file
target = native          # or riscv64
```

In a project directory, `keelc run`, `keelc check`, `keelc build` and `keelc qemu` need no file
argument. `ref/examples/project/` is an example with nested modules and private helpers.

## The prelude

Every program starts with the declarations in `ref/src/Keel/Prelude.hs`, written in Keel:

| Name | What it is |
|---|---|
| `List a` | `Nil \| Cons(a, Box (List a))`; string literals are `List u8` |
| `map`, `foldl` | the usual, effect-polymorphic in the function argument |
| `length`, `append`, `reverse` | list utilities |
| `print`, `println` | print a `List u8` (`println` adds a newline) |
| `printInt`, `printU64` | print a number in decimal, without a newline |

A program may declare any of these names itself. The prelude's version is then left out, along
with every prelude definition that mentions a left-out or redeclared name. A program that defines
its own `List`, or its own `putc` UART driver, gets none of the prelude's list or printing
functions instead of ones silently built on its definitions. Unused prelude definitions cost
nothing: the optimizer removes them.

## Error messages

Errors name the file, line and column of the innermost expression involved, and show the line:

```
twice.kl:5:7: error [Duplicate]: ["t"] used twice
5 |   \t. consume t + consume t
          ^
```

This covers errors from inference and from the core checker (linearity, effects, references).
Parts elaborated from `&`/`&mut`/`var` code keep the position of the nearest enclosing
expression without references.

## Hardware access

**MMIO** is a built-in effect, like `IO`:

| Operation | Type |
|---|---|
| `read8(addr)`, `read32(addr)` | `u64 => u8`, `u64 => u32` |
| `write8(addr, v)`, `write32(addr, v)` | `(u64, u8) => Unit`, `(u64, u32) => Unit` |

Unhandled, the machine performs them as real (volatile) memory accesses: only on the
freestanding RISC-V target; on the Mac and in the evaluator an unhandled MMIO operation panics.
Handled, they are an ordinary effect, so a driver can be tested against a mock device:
`examples/uart.kl` and `examples/firmware/hello.kl` are the same driver, mocked and on QEMU.

**bitdata** declares a register layout over an integer type: fields are a bit (`@ 5`) or an
inclusive range (`@ 1..2`). A bitdata type is distinct from its integer while type checking
(a `LineStatus` can't be passed where a `u8` is expected) and is the plain integer at run time:
field reads compile to a shift and a mask.

## What inference fills in

Keel Core is explicitly typed (`spec/core.md` §4.1). Inference supplies:

- **λ parameter types**, from the type the λ is checked against or from how the parameter is
  used. Top-level definitions always have a declared type, so their λs are checked.
- **Literal widths**: from context, otherwise `i64`.
- **Type arguments** of constructors, cocases and polymorphic definitions, by unification.
- **Effect arguments** of polymorphic definitions: an effect variable gets the union of the
  effects that flow into it. `map (\n. n * 10) xs` instantiates `'e := {Panic}`.
- **λ vs λ°**: a λ that captures a linear value is linear.
- **Operations**: `read(4)` is `Perform read 4` when `read` is an operation, not a variable.
- **Shadowing**: allowed; binders are renamed apart (`x~1`), since the core forbids it.

Inference only fills in annotations. The result goes through the full core checker, which has
the final word on linearity, effects and references.

## Limits

- `e.obs` needs `e`'s codata type to be known at that point; add an annotation if it isn't.
- Strings are lists of bytes: simple and uniform, but each character is a heap cell.
