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
  p-8   │ header: layout (bits 0–9)                 │   which constructor, words, pointer map
        │         count (10–30)                     │   moves by 1024; 0: freed
        │         immortal (31)                     │   static blocks, and overflowed counts
        │         the field, or words (32–39)       │   layouts from 512: a narrow field
        │         and pointer map (40–55)           │   below: bit i = payload word i
        ├──────────────────────────────────────────┤
  p     │ fields | code pointer                     │
  p+8   │ … | captured values                       │
        └──────────────────────────────────────────┘
```

| Block | Payload |
|---|---|
| data value | its fields, one word each, but the first narrow one: that one is in the header |
| pair | `[first, second]` |
| closure | `[code, captured₁, …]` |
| codata value | `[code₁, …, codeₙ, captured₁, …]` (one function per observation) |
| array | `[length, capacity, element₀, …]` |

**Layouts.** Lowering numbers every shape of block in the program: each constructor at each
field layout (`Some` at `i64` and at `i32` are two), and each size and pointer map of the other
blocks. A `case` compares layout ids. The runtime needs a block's words and pointer map to free
it: for most layouts the header's high half holds them; a data block whose layout puts its
first **narrow field** (an integer of at most 32 bits, or a `Bool`) in the high half instead
gets a layout id from 512 up, and the runtime looks those up in a table. So `Leaf(i32)` is 8
bytes, the header alone, and `Node(i32, Box T, Box T)` 24. A program may have 510 layouts of
each kind.

**Packed layouts** (AArch64 only). A constructor with two or more pointer fields keeps its word
fields first and then each pointer in a 4-byte slot holding `(child − block) / 8`, signed: so
`Node(i32, Box T, Box T)` is 16 bytes, `Node(Box T, Box T)` too. Bit 16 of the pointer map
(header bit 56, or table bit 24) marks the layout, and its map's bits are then 4-byte slots.
A slot reaches ±16 GB, which covers every heap block and the static blocks just below the
heap, since the native heap is 15 GB. RISC-V and x86-64 lower without packing.

An **array** has layout 509 when its elements are narrow (an integer of at most 32 bits, or a
`Bool`: 4 bytes each, so `Array i32` holds two per word), 510 for other words, 511 when they
are pointers. Its words field is 2 + its capacity's elements in words, capped at 255 (blocks
that large are never recycled).

The **count** has 21 bits. One that overflows (2 million references to one block) carries into
the immortal bit: the block is never freed. A free block keeps its free-list link in its first
word, or, with no words, in the header's high half (in words from itself).

Top-level definitions are static blocks in the data section with an immortal header: counting
skips them. So is each constructor without fields (`Nil`, `None`, `Leaf`): one static block
per layout, shared by every use.

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

On AArch64, when a `case` proves that all pointer fields are transferred, a unique parent's
drop-to-token operation is emitted inline. The runtime count check includes the immortal bit;
shared or immortal parents, invalid counts and partial transfers still go through the generic
helper. This preserves the header's narrow field, arena behavior and allocator statistics.
See [the paired measurements](perf.md#full-field-constructor-reuse-aarch64-2026-10-22).

**Arrays** work the same way, without a token: `arraySet`, `arrayPush` and `arrayPop` take the
array owned and update it in place when its count is 1; otherwise they copy it first (duplicating
the elements) and decrement the original. `arrayGet` and `arrayLength` borrow the array, like a
field read, so `let x = arrayGet xs i in arraySet xs i (x + 1)` leaves `xs` unique and updates in
place. A full array doubles its capacity on push: in place when it is unique and the last block
before the bump pointer (AArch64), otherwise into a new block; when it was unique, the elements
move there and the old one is freed without touching them. `test/std/array.kl` does 200,000 pushes
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

## Arenas

`arena (\u. e)` evaluates `e` and frees everything it allocated at once (the arena rows of
Goose's benchmarks, and the "compile-time-sized arenas" of M2, without the compile-time size).
Opening one records the bump pointer; while any is open, allocation skips the free lists (so
everything allocated inside lies above that mark) and `drop` leaves blocks above the outermost
open arena's mark alone: no child walk, no free list. Closing resets the bump pointer to the
mark. Arenas nest; an inner one's memory is reused by the outer one after it closes.

Nothing allocated inside may survive, which keelc checks when lowering: the result and every
captured local are not pointers, and `e` performs only built-in effects (a user handler's clause
could hand a pointer in or out). Counting still happens inside (in-place updates need it), and
the statistics count an arena's blocks as freed when it closes, so `live=0` still holds.

## Measured

| Program | Fresh | Recycled | In place | Live at exit |
|---|---|---|---|---|
| `examples/reuse.kl` (1M cell rebuilds) | 1,004 | 1,003,999 | 1,001,000 | 0 |
| 10M pairs in a 64 MB heap (would need 320 MB) | 2 | 19,999,999 | 0 | 0 |

The recycled blocks in `reuse.kl` are curried partial applications (`map f` builds a closure per
call); known-arity calls (M4) remove them.

## Limits and next steps

- **Done since:** reuse across branches (a token goes into an if's or a case's branches when
  each of them allocates a block its size) and fusing a field's dup with the parent's drop when
  the parent is unique (the fields' duplicates become a mask the runtime only acts on for a
  shared parent): insertion sort 0.63×, `map` 0.76×. **Not yet:** specialized drop functions,
  and dropping a unique parent whose fields are taken over without a reuse (a plain drop).
  These are standard Perceus refinements that remove counting work; none changes the model.
- A block may have at most 16 payload words before its last pointer (the pointer map is
  16 bits); larger blocks are rejected at compile time. Arrays have no such limit.
- Only a block's first narrow field moves into the header; the others take a word each
  (packing two `i32` fields into one word is the next step). Counts have 21 bits: a block with
  more than 2 million references becomes immortal and leaks.
- Blocks over 64 words, so arrays of more than 62 elements, are not recycled: a growing array
  that isn't the last block (or on RISC-V) leaves its smaller copies behind in the bump region. A free list for large blocks (first fit,
  or size classes by powers of two) is the fix when a program runs out of heap.
- Counts are not atomic: fine for single-core code; multicore sharing needs atomic counts or
  ownership transfer (`notes.md` §16, concurrency).
- **Real-time code** (`notes.md` §13): a drop can free a whole structure, which takes time
  proportional to its size. Code with timing bounds should use linear values and arenas, where
  the cost is known; reference counting already has the `Alloc` effect for that reason.
