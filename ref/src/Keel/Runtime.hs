-- | The runtime routines the three back ends share, written once against "Keel.Asm"
-- (spec/backends.md). Each back end's @emitRuntime@ calls these with its own emitters; what
-- only one target has (host I/O, sockets, RISC-V printing and traps) stays there.
module Keel.Runtime (arenaOpen) where

import Keel.Asm

-- | Arenas (spec/memory.md). Opening one takes a record [base before, enclosing record, bump
-- allocations so far] from the bump pointer; while any is open, _keel_drop leaves blocks at
-- or above _keel_arena_base (the outermost record) alone, and _keel_alloc takes everything
-- from the bump pointer. Closing resets the bump pointer to the record: everything allocated
-- since is freed at once, and counted as freed.
arenaOpen :: Monad m => Asm m -> m ()
arenaOpen a = do
  fn a "_keel_arena_open"
  addr a (T 0) "_keel_heap_ptr"
  load a Word (T 1) (T 0) 0 -- the record
  op a Add (T 2) (T 1) (I 24)
  load a Word (T 3) (T 0) 8
  branch a Gtu (T 2) (R (T 3)) "_keel_panic_oom"
  store a Word (T 2) (T 0) 0
  addr a (T 0) "_keel_arena_base"
  load a Word (T 2) (T 0) 0
  store a Word (T 2) (T 1) 0
  addr a (T 3) "_keel_arena_top"
  load a Word (T 4) (T 3) 0
  store a Word (T 4) (T 1) 8
  store a Word (T 1) (T 3) 0
  addr a (T 4) "_keel_stats"
  load a Word (T 4) (T 4) 0
  store a Word (T 4) (T 1) 16
  -- The base is the outermost record: the lowest (none is all ones).
  branch a Ltu (T 2) (R (T 1)) keep
  store a Word (T 1) (T 0) 0
  label a keep
  -- Everything from the bump pointer while it is open: an empty free-list table.
  addr a (T 0) "_keel_nofree"
  addr a (T 1) "_keel_fl"
  store a Word (T 0) (T 1) 0
  mov a (A 0) (I 0)
  ret a
  where
    keep = local a "arena_keep"
