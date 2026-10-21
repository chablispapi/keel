# Keel surface syntax

The language you write in `.kl` files. `keelc` parses it (`ref/src/Keel/Parser.hs`), infers what
Keel Core needs explicitly (`ref/src/Keel/Infer.hs`), then runs the core pipeline of
`spec/core.md`. Examples are in `ref/examples/`.

```
keelc check FILE.kl            type-check; print main's type and effects
keelc run   FILE.kl            run with the reference evaluator
keelc asm   FILE.kl            print the ARM64 assembly
keelc build FILE.kl [-o OUT]   compile to a native executable (via the system cc)
```

## Programs

A file is a list of declarations followed by `main = expression`. Comments are `-- …` and `{- … -}`.

```
[linear] data List a = Nil | Cons(a, Box (List a))
codata Ord a { lt : a -> a -> Bool }
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
| `read(4)`, `out(x)` | performing an operation |
| `Cons(1, box Nil)`, `box e`, `unbox e`, `(a, b)` | constructors, boxes, pairs |
| `42`, `250u8`, `-5`, `true`, `()` | literals (width inferred unless suffixed) |
| `+ - *`, `+% -% *%`, `+\| -\| *\|`, `+? -? *?` | checked, wrapping, saturating, Option arithmetic |
| `==`, `<` | comparisons |
| `f[i64]`, `Nil[i64]` | explicit type arguments (usually inferred) |

Precedence, loosest first: `;`, then `λ` / `let` / `var` / `if` / `handle` / `:=` (their bodies
extend as far as possible), then `==` `<`, then `+ -` (all variants), then `* `, then
application, then `.obs` and `[types]`. A `-` directly before a number at the start of an
operand is a negative literal; `n -1` still means `n - 1`.

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

## Limits (M1)

- `e.obs` needs `e`'s codata type to be known at that point; add an annotation if it isn't.
- Effect handlers run in the evaluator (`keelc run`) but are not compiled natively until M3.
- Error messages report the kind of error and the types involved, not yet source positions
  for type errors (parse errors do have positions).
