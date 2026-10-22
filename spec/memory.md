# Keel memory model (M2)

Keel has no garbage collector. Heap memory is managed by **reference counting inserted at
compile time**, in the style of Perceus (Koka) and Lean 4, with **in-place reuse**: when a
function takes apart a value nothing else references and builds a new one of the same size,
the old block is updated in place. Implementation: `ref/src/Keel/Lower.hs` (`refcount`) and
the runtime in `ref/src/Keel/AArch64.hs` (`emitRuntime`).

## Why reference counting is enough

Keel's heap is **acyclic by construction**. Values are immutable, evaluation is strict, `&mut`
is pure state passing (`spec/core.md` §3), and recursion goes through top-level definitions,
whose blocks are static. A block can only point to blocks that existed before it, so counting
references frees everything; there are no cycles for a collector to find. Linear types
(`spec/core.md` §1) guarantee that resources are released exactly once; reference counting
handles ordinary shared data.

## Heap blocks

Every value is one 64-bit word. Integers, `Bool` and `Unit` are stored directly. Data values,
pairs, closures and codata values are pointers to heap blocks. `Box` is the identity.

```
        ┌──────────────────────────────────────────┐
  p-8   │ header: count (bits 0–31)                 │   bit 31 set: immortal (static block)
        │         size in words (32–39)            │   count 0: freed
        │         tag (40–47)                       │   the constructor; 255: an array
        │         pointer map (48–63)              │   bit i: payload word i is a pointer
        ├──────────────────────────────────────────┤
  p     │ fields | code pointer                     │
  p+8   │ … | captured values                       │
        └──────────────────────────────────────────┘
```

| Block | Payload |
|---|---|
| data value, pair | `[field₁, …, fieldₙ]` (the tag is in the header) |
| closure | `[code, captured₁, …]` |
| codata value | `[code₁, …, codeₙ, captured₁, …]` (one function per observation) |
| array | `[length, capacity, element₀, …]` |

An **array** has tag 255, and its pointer map is not a map: bit 1 says whether the elements are
pointers. Its size field is capacity + 2, capped at 255 (blocks that large are never recycled).

Top-level definitions are static blocks in the data section with an immortal header: counting
skips them. So is each constructor without fields (`Nil`, `None`, `Leaf`): one static block
per tag, shared by every use.

## Ownership

Every pointer variable **owns** one reference. The calling convention is all-owned:

- a function receives its argument **owned**, and also **owns its closure block**: on entry it
  copies out the captured values, duplicates the captured pointers, and drops the block;
- a function returns an **owned** result;
- storing a value in a block, passing it, or returning it **consumes** that reference;
- reading a field (`case`, `let (x, y)`) **borrows** the block; the field is then duplicated
  so the variable owns it.

Two exceptions, both inferred by the compiler (`Lower.borrowSigs`, after Lean):

- a function that is only ever called directly (never as a closure) **borrows** a pointer
  parameter it only reads: the caller keeps the value alive across the call, and nothing is
  counted. A parameter stays owned if the function consumes it, could reuse its block, or
  receives an owned value for it in a tail call (which would otherwise stop being a jump);
- a field read from a borrowed value is borrowed too, not duplicated.

`let y = x` makes `y` another name for the same reference.

Owning the closure keeps calls in tail position: nothing is left to drop after the call, so
`loop (i - 1) (acc + i)` still compiles to a jump (constant stack).

## Inserting dup and drop

A backward liveness pass over the lowered code (`refcount`) places the operations. For each
statement and each pointer variable `v` in scope:

| Situation | Inserted |
|---|---|
| `v` consumed `c` times here and used again later | `c` dups before |
| `v` consumed `c` times here and dead afterwards | `c - 1` dups before |
| `v` only read here (field access) and dead afterwards | drop after |
| `v` unused here and dead afterwards | drop before |
| a branch of `if`/`case` | variables not needed after the join are dropped inside each branch |

Every variable is therefore dropped right after its last use, not at the end of its scope.

## In-place reuse

When a `case` scrutinee dies inside a branch, and that branch later allocates a block of the
same size in straight-line code, the drop becomes a **reuse token**:

```
case xs of Cons(x, rest) -> Cons(f x, box (map f (unbox rest)))

  x, rest  = fields of xs (owned)
  tok      = drop_reuse(xs)       if xs is unique: its block, else 0 (and xs is decremented)
  …                               the calls
  new cell = alloc_at(tok, Cons)  in place when tok ≠ 0, otherwise a fresh allocation
```

With a unique list, `map` rewrites every cell in place: `examples/reuse.kl` maps a 1,000-element
list 1,000 times with about 1,000 fresh allocations and 1,001,000 in-place updates. With a shared
list the same code allocates, so the shared copy is never changed. This is how pure code gets
mutation's performance without any `&mut`.

**Arrays** work the same way, without a token: `arraySet`, `arrayPush` and `arrayPop` take the
array owned and update it in place when its count is 1; otherwise they copy it first (duplicating
the elements) and decrement the original. `arrayGet` and `arrayLength` borrow the array, like a
field read, so `let x = arrayGet xs i in arraySet xs i (x + 1)` leaves `xs` unique and updates in
place. A full array doubles its capacity on push; when it was unique, the elements move to the
new block and the old one is freed without touching them. `test/std/array.kl` does 200,000 pushes
and 100,000 updates with 36 allocations.

## Runtime

- **Allocation:** blocks up to 64 payload words come from **size-segregated free lists**, then
  from a bump region (64 MB). Running out is a panic.
- **Drop:** decrements the count; at zero it drops the children named by the pointer map (an
  array's elements, if they are pointers) and frees the block. The last pointer child is handled by looping instead of recursing, so freeing
  a long list uses constant stack.
- **Checks:** duplicating or dropping a freed block (count 0) is a panic ("reference count
  error"), so a double free cannot go unnoticed.
- **Statistics:** with `KEEL_STATS=1`, a program reports on stderr
  `allocs recycled inplace freed live`. The native test suite runs every program this way and
  requires `live=0` at exit: **no program leaks**.

## Measured

| Program | Fresh | Recycled | In place | Live at exit |
|---|---|---|---|---|
| `examples/reuse.kl` (1M cell rebuilds) | 1,004 | 1,003,999 | 1,001,000 | 0 |
| 10M pairs in a 64 MB heap (would need 320 MB) | 2 | 19,999,999 | 0 | 0 |

The recycled blocks in `reuse.kl` are curried partial applications (`map f` builds a closure per
call); known-arity calls (M4) remove them.

## Limits and next steps

- **Not yet:** borrow inference for parameters, fusing a field's dup with the parent's drop when
  the parent is unique, reuse across branches, and specialized drop functions. All of these are
  standard Perceus refinements that remove counting work; none changes the model.
- A block may have at most 16 payload words before its last pointer (the pointer map is
  16 bits); larger blocks are rejected at compile time. Arrays have no such limit.
- Blocks over 64 words, so arrays of more than 62 elements, are not recycled: a growing array
  leaves its smaller copies behind in the bump region. A free list for large blocks (first fit,
  or size classes by powers of two) is the fix when a program runs out of heap.
- Counts are not atomic: fine for single-core code; multicore sharing needs atomic counts or
  ownership transfer (`notes.md` §16, concurrency).
- **Real-time code** (`notes.md` §13): a drop can free a whole structure, which takes time
  proportional to its size. Code with timing bounds should use linear values and arenas, where
  the cost is known; reference counting already has the `Alloc` effect for that reason.
