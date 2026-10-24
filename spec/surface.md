# Keel surface syntax

The language you write in `.kl` files. `keelc` parses it (`ref/src/Keel/Parser.hs`), infers what
Keel Core needs explicitly (`ref/src/Keel/Infer.hs`), then runs the core pipeline of
`spec/core.md`. Examples are in `ref/examples/`.

```
keelc new NAME                 create a project: NAME/keel.project, NAME/src/main.kl
keelc check [FILE.kl]          type-check; print main's type and effects
keelc run   [FILE.kl]          run with the reference evaluator
keelc asm   [FILE.kl] [-g]     print the ARM64 assembly
keelc build [FILE.kl] [-o OUT] [--target native|riscv64|x86_64] [-g]
                               native executable (assembled by Homebrew's LLVM clang if
                               installed, else the system cc; linked by cc), a freestanding
                               RISC-V image for QEMU's virt board, or x86-64 Linux assembly;
                               -g adds debug info
keelc qemu  [FILE.kl]          build for RISC-V and boot it in QEMU
keelc lsp                      the language server, over stdin/stdout
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
| `Array a` | built-in growable array of `Free` elements (see the standard library) |
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
| `case e of { Nil -> a \| Cons(x, rest) -> b }` | pattern matching (a case on a `Box` is a case on its contents) |
| `case t of { Node(l, x, r) -> x \| _ -> 0 }` | a last `_ -> e` (or `y -> e`, `y` being the scrutinee) covers the constructors not listed (one default branch in Keel Core; a body covering a single constructor becomes that constructor's branch) |
| `case xs of { Cons(a, Cons(b, _)) -> a + b \| Cons(a, Nil) -> a \| _ -> 0 }`, `case (p, q) of { (Some(x), Some(y)) -> … \| _ -> 0 }` | nested patterns (constructors, pairs, variables and `_` inside each other): flat cases, each alternative falling through to the next when an inner pattern fails. A field pattern looks inside a `Box` field; a variable still binds the box. The scrutinee is tested again on fallthrough, so a fallthrough needs a non-linear value. Literal patterns stay at the top level |
| `case c of { '(' -> 1 \| 42 -> 2 \| -1 -> 3 \| _ -> 0 }` | literal patterns: an `if` chain on `==`, which needs a last `_ -> e` or `y -> e` |
| `cocase Ord { lt -> \p q. p < q }`, `e.lt` | codata value, observation |
| `handle e with MMIO { read a -> e \| write w -> e }` | handler |
| `read8(4)`, `out(x)`, `putc(c)` | performing an operation (`out` prints a number and a newline, `putc` one byte) |
| `getc ()` | read one byte of input (effect `Input`): `0`–`255`, or `-1` at the end |
| `Cons(1, box Nil)`, `box e`, `unbox e`, `(a, b)` | constructors, boxes, pairs |
| `42`, `250u8`, `0x1000_0000`, `-5`, `true`, `()` | literals (width inferred unless suffixed; `_` separates digits) |
| `"Hi!\n"` | a `List u8` of the string's UTF-8 bytes (Haskell-style escapes) |
| `'a'`, `'\n'` | an ASCII character as a `u8` (in expressions only; in types `'a` is an effect variable) |
| `/`, `%` | division truncating toward zero, remainder; panic on division by zero and `min / -1` |
| `x land y`, `lor`, `lxor`, `lsl`, `lsr` | bitwise and, or, xor, shifts (logical for unsigned types, arithmetic for signed) |
| `e as u8` | wrapping conversion between integer types |
| `s.thr_empty`, `s.raw`, `LineStatus(x)`, `LineStatus { thr_empty = 1 }` | bitdata field, raw value, from raw, from fields |
| `+ - *`, `+% -% *%`, `+\| -\| *\|`, `+? -? *?` | checked, wrapping, saturating, Option arithmetic |
| `==`, `<`, `!=`, `>`, `<=`, `>=` | comparisons (the last four are written with `==`, `<` and `if`; operands still evaluate left to right) |
| `a && b`, `a \|\| b`, `not a` | `if a then b else false`, `if a then true else b`, and a prelude function |
| `f[i64]`, `Nil[i64]` | explicit type arguments (usually inferred) |

Precedence, loosest first: `;`, then `λ` / `let` / `var` / `if` / `handle` / `:=` (their bodies
extend as far as possible), then `||`, then `&&` (both associate to the right), then the
comparisons, then `+ -` (all variants), then `*` and the bitwise
operators, then `as`, then application, then `.obs` and `[types]`. A `-` directly before a number at the start of an
operand is a negative literal; `n -1` still means `n - 1`.

## Projects and modules

**Modules.** One file is one module. A file starts with its imports:

```
import util                  -- util.kl
import drivers.console       -- drivers/console.kl, known as console
import drivers.led as light  -- drivers/led.kl, known as light
```

Paths are relative to the entry file's directory, and imports load transitively. Only the entry
file may define `main`.

**Names.** A module sees its own declarations, the public declarations of the modules it
imports, and the prelude. An imported name can be used plain (`greet`) or qualified by its
module (`console.greet`, `light.init`). Two imported modules may declare the same name; a plain
use is then ambiguous, and the qualified form picks one:

```
main.kl:8:8: init is ambiguous: it is declared in drivers.console and drivers.led; write console.init or light.init
```

An imported name the prelude also has is ambiguous the same way: after `import std.array`, a
plain `length` is an error, and `array.length` or `prelude.length` picks one. Importing a
module never changes what a prelude name means; only the entry file can replace a prelude
definition, by declaring the name itself.

A declaration marked `private` is visible only in its own file, so two modules can each have a
`private def helper`. A qualifier wins over a projection only when no local variable has that
name: with a local `console`, `console.greet` observes it. Types, constructors and effects are
qualified the same way, in types, expressions and patterns:

```
def code : uart.Status -> i64 = \s. case s of { uart.Ready -> 0 | uart.Busy(n) -> n }
main = handle poll () with uart.Port { get u -> 1 }
```

The operations in a handler's clauses are written plain; an operation name two imported
effects share can't be handled yet.

The loader reports import cycles (`import cycle: a → b → a`), missing modules (at the
`import`), names from a module that isn't imported (`hidden is declared in module b; import b
to use it`), and qualified uses of private or missing names.

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
| `readAll` | every byte of input, as a `List u8` (effect `Input`) |
| `Ordering`, `compareInt` | `Less \| Equal \| Greater`, and comparing `i64`s |
| `not` | Boolean negation |

A program may declare any of these names itself. The prelude's version is then left out, along
with every prelude definition that mentions a left-out or redeclared name. A program that defines
its own `List`, or its own `putc` UART driver, gets none of the prelude's list or printing
functions instead of ones silently built on its definitions. Unused prelude definitions cost
nothing: the optimizer removes them.

## The standard library

Modules under `std` ship with keelc (`ref/std/`, installed with it) and are imported like any
other: `import std.map`, then `map.insert`.

| Module | What it has |
|---|---|
| `std.map` | `Map k v`: ordered maps (AVL trees). `Tip` is the empty map; `insert`, `lookup`, `member`, `delete` take a comparison (`compareInt`, `string.compare`); `size`, `height`, `toList` (in key order) |
| `std.array` | `Array a`: growable arrays with constant-time indexing. `empty`, `make n x`, `length`, `get`, `set`, `push`, `pop`, `fromList`, `toList`, `foldl` |
| `std.file` | `read path`: a file's bytes as `Option (List u8)` (`None` if it can't be opened); `write path bytes` and `appendTo path bytes` (`false` if it can't be written); `open`, `getByte`, `create`, `openAppend`, `put`, `close` to stream (effect `Files`) |
| `std.loop` | an event loop: `run init step` drives a pure `step : s -> Event -> (s, List Command)`. Events: `Start`, `Listening`, `Accepted`, `Connected`, `Failed`, `Received`, `Closed`, `Timer`; commands: `Listen`, `Connect`, `Send`, `Close`, `After`, `Stop`; `ipv4 127 0 0 1` (effect `Net`; `examples/echo.kl`, `examples/timers.kl`) |
| `std.string` | for `List u8`: `compare`, `equal`, `fromInt`, `parseInt` (`Option i64`), `split`, `lines`, `join`, `isDigit`, `isSpace`, `isAlpha` |

```
import std.map
import std.string

def count : List (List u8) -> map.Map (List u8) i64 ->{Diverge, Panic} map.Map (List u8) i64 =
  \ws m. case ws of
    { Nil -> m
    | Cons(w, rest) ->
        let n = case map.lookup string.compare w m of { None -> 0 | Some(k) -> k } in
        count (unbox rest) (map.insert string.compare w (n + 1) m) }
```

`examples/words.kl` counts the words on stdin this way. Keys and values are `Free`
(copyable).

**Arrays** are values: `array.set xs 0 x` returns an array and leaves `xs` as it was. Under the
hood an array nothing else references is updated in place, so a loop that threads one array
through `set` and `push` runs as fast as mutation (spec/memory.md). The built-in operations are
`arrayEmpty`, `arrayNew`, `arrayLength`, `arrayGet`, `arraySet`, `arrayPush` and `arrayPop`,
always applied to all their arguments; `std.array` has them as functions. An index out of range
panics.

**Arenas:** `arena (\u. e)` is `e`, but everything `e` allocates is freed at once when it returns
instead of block by block (spec/memory.md, "Arenas"). keelc only accepts it when nothing
allocated inside can escape: the result and every local `e` uses must not be pointers (data,
pairs, closures, arrays), and `e` may perform only built-in effects. For example, building a
tree, measuring it and dropping it: `arena (\u. size (build 20))`.

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

## Editor support

`keelc lsp` is a language server (LSP over stdin/stdout):

- **Diagnostics** while you type: parse, module and type errors, from unsaved buffers too. A
  file in a project (a `keel.project` in its directory or above) is checked as part of the
  project, from the project's entry file.
- **Hover** shows the declared type of a top-level name: definitions, constructors and effect
  operations, from the program, the prelude or the built-in effects.
- **Go to definition** jumps to where a top-level name is declared, in this file or an
  imported module (`uart.putc` looks in the module imported as `uart`); on an `import` line,
  to the imported file. Helix: `gd`. It matches by name, so a local variable that shadows a
  top-level name jumps to the top-level one, and prelude names go nowhere.

Put `keelc` on your `PATH` (`cabal install exe:keelc` in `ref/`), then point the editor at it.
For Neovim:

```lua
vim.filetype.add({ extension = { kl = "keel" } })
vim.api.nvim_create_autocmd("FileType", { pattern = "keel", callback = function()
  vim.lsp.start({ name = "keel", cmd = { "keelc", "lsp" },
    root_dir = vim.fs.root(0, { "keel.project" }) or vim.fn.getcwd() })
end })
```

For Helix (`languages.toml`):

```toml
[language-server.keel]
command = "keelc"
args = ["lsp"]

[[language]]
name = "keel"
scope = "source.keel"
file-types = ["kl"]
roots = ["keel.project"]
language-servers = ["keel"]
```

For Claude Code, `editors/claude-code/` is a plugin with the language server and a skill for
writing Keel (the workflow, common mistakes, and examples the test suite runs). The repository
is its marketplace. Install it once for every project:

```
claude plugin marketplace add ~/playground/fp     # the repository root
claude plugin install keel@keel
```

It loads in place from the repository, so edits to the skill apply in the next session.

Syntax highlighting is a tree-sitter grammar in `editors/tree-sitter-keel/` (`grammar.js`,
`queries/highlights.scm`). For Helix, build it into the runtime directory and link the queries:

```
cd editors/tree-sitter-keel
tree-sitter generate              # after editing grammar.js
tree-sitter build -o ~/.config/helix/runtime/grammars/keel.so .
ln -sfn "$PWD/queries" ~/.config/helix/runtime/queries/keel
```

Not yet: types of local variables on hover, completion.

## Debugging

`keelc build -g` adds DWARF debug info to a native build (`OUT.dSYM` next to the executable),
so lldb can break on `.kl` lines, show the source, and name Keel functions in backtraces:

```
$ keelc build -g examples/fact.kl && lldb examples/fact
(lldb) b fact.kl:4
(lldb) run
-> 4     \n. if n < 1 then 1 else n * fact (n - 1)
                ^
(lldb) bt
  * frame #0: fact`fact at fact.kl:4:10
    frame #1: fact`fact at fact.kl:4:32
    frame #2: fact`main at fact.kl:9:12
```

The program is optimized as usual. Inlined code keeps its own lines, so a breakpoint on a
small inlined function stops in its caller. A line with no code of its own left after
inlining (`\n. helper n n`, once `helper` is inlined) takes no breakpoint. Stepping and
breakpoints work; lldb can't print Keel values yet (no variable locations or types), and the
RISC-V target has no debug info yet.

## Hardware access

**Input** has one operation, `getc : Unit => i64`: stdin on the Mac and in the evaluator
(`keelc run` passes its stdin through); on RISC-V, the UART's receive register, with `-1` when no
byte is waiting.

**Files** reads and writes files by name: `openFile : Array u8 => i64` (a handle to read, or
-1), `readByte : i64 => i64` (a byte, or -1 at the end), `createFile` and `appendFile : Array u8
=> i64` (a handle to write: the file emptied, or written after its end), `writeBytes : (i64,
Array u8) => i64` (how many bytes, or -1), `closeFile : i64 => Unit`. On the Mac and on x86-64
Linux they are `fopen`, `fgetc`, `fputc` and `fclose`, with paths relative to the current
directory. `keelc run` reads the same files; what a program writes it reads back as written,
and the files are saved when it ends. RISC-V has no file system, so every open there gives -1.
Use `std.file` rather than the handles: `examples/files.kl`, `examples/write.kl`.

**Net** is IPv4 TCP and a clock, as thin socket calls: `tcpListen (address, port)`,
`sockPort`, `tcpAccept`, `tcpConnect (address, port)`, `sockSend (fd, (bytes, from))` (how
many bytes from `from` on the socket took without waiting), `sockRecv fd` (an `Array u8`,
empty when the peer has closed), `sockClose`, `pollWait (fds, timeout)` (each entry `fd · 4 +
1 to read + 2 to write`; the first ready one as `index · 4 + readable + 2 · writable`, -1 on timeout,
-2 when it can't wait) and `clockMs`. On the Mac and on x86-64 Linux they are the C library's
sockets and `poll`; `keelc run` simulates a loopback network inside the program (connections
only to its own listeners, 64 KiB of buffer per socket, and a clock that moves only when it
waits); on RISC-V every listen and connect fails. Use `std.loop` rather than the operations:
its `Send` queues what a connection can't take yet (`examples/bulk.kl`).

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
