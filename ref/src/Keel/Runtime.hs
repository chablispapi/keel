-- | The runtime routines the three back ends share, written once against "Keel.Asm"
-- (spec/backends.md). Each back end's @emitRuntime@ calls these with its own emitters; what
-- only one target has (host I/O, sockets, RISC-V printing and traps) stays there.
module Keel.Runtime (alloc, arenaOpen, arenaClose) where

import Control.Monad (when)
import Keel.Asm

-- | _keel_alloc: A 0 = payload words, A 1 = header without its count (on RV32 its low half,
-- and A 2 the high one) → A 0 = payload. Clobbers T 0–3 only. Blocks of up to @maxSmall@
-- words come from their size's free list, unless an arena is open (the table is then empty);
-- the rest from the bump pointer.
alloc :: Monad m => Asm m -> Integer -> m ()
alloc a maxSmall = do
  fn a "_keel_alloc"
  mov a (T 0) (I maxSmall)
  branch a Gtu (A 0) (R (T 0)) bump
  loadSym a (T 0) "_keel_fl" -- the free lists, or an empty table while an arena is open
  loadIx a (T 1) (T 0) (A 0) 3
  branch a Eq (T 1) (I 0) bump
  branch a Eq (A 0) (I 0) link0
  load a Word (T 2) (T 1) 0 -- the next free block
  label a pop
  storeIx a (T 2) (T 0) (A 0) 3 (T 3)
  stat a 8 (T 2) (T 3)
  jump a header
  label a bump
  addr a (T 0) "_keel_heap_ptr"
  load a Word (T 1) (T 0) 0
  addScaled a (T 2) (T 1) (A 0) wordShift
  op a Add (T 2) (T 2) (I 8)
  load a Word (T 3) (T 0) 8
  branch a Gtu (T 2) (R (T 3)) "_keel_panic_oom"
  store a Word (T 2) (T 0) 0
  op a Add (T 1) (T 1) (I 8)
  stat a 0 (T 2) (T 3)
  label a header
  op a Or (T 2) (A 1) (I 1024) -- count 1
  store a Word (T 2) (T 1) (-8)
  when (wordBytes a == 4) $ store a Word (A 2) (T 1) (-4)
  mov a (A 0) (R (T 1))
  ret a
  -- A block of no words links to the next in its header's high half, in words from it.
  label a link0
  load a (Half32 True) (T 2) (T 1) (-4)
  branch a Eq (T 2) (I 0) pop
  addScaled a (T 2) (T 1) (T 2) wordShift
  jump a pop
  where
    wordShift = if wordBytes a == 4 then 2 else 3
    bump = local a "alloc_bump"
    pop = local a "alloc_pop"
    header = local a "alloc_header"
    link0 = local a "alloc_link0"

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

arenaClose :: Monad m => Asm m -> m ()
arenaClose a = do
  fn a "_keel_arena_close"
  addr a (T 0) "_keel_arena_top"
  load a Word (T 1) (T 0) 0 -- the record
  load a Word (T 2) (T 1) 8
  store a Word (T 2) (T 0) 0
  load a Word (T 2) (T 1) 0 -- the base before it
  addr a (T 3) "_keel_arena_base"
  store a Word (T 2) (T 3) 0
  -- Allocated inside: freed now…
  addr a (T 3) "_keel_stats"
  load a Word (T 0) (T 3) 0
  load a Word (T 4) (T 1) 16
  op a Sub (T 0) (T 0) (R (T 4))
  load a Word (T 4) (T 3) 24
  op a Add (T 4) (T 4) (R (T 0))
  store a Word (T 4) (T 3) 24
  -- … and not again when the enclosing arena closes.
  load a Word (T 4) (T 1) 8
  branch a Eq (T 4) (I 0) outermost
  load a Word (T 5) (T 4) 16
  op a Add (T 5) (T 5) (R (T 0))
  store a Word (T 5) (T 4) 16
  label a outermost
  addr a (T 3) "_keel_heap_ptr"
  store a Word (T 1) (T 3) 0
  -- The outermost arena closed (the base before it is all ones): the free lists are back.
  op a Add (T 4) (T 2) (I 1)
  branch a Ne (T 4) (I 0) done
  addr a (T 0) "_keel_freelists"
  addr a (T 3) "_keel_fl"
  store a Word (T 0) (T 3) 0
  label a done
  mov a (A 0) (I 0)
  ret a
  where
    outermost = local a "close_outermost"
    done = local a "close_ret"
