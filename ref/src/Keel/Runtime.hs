-- | The runtime routines the three back ends share, written once against "Keel.Asm"
-- (spec/backends.md). Each back end's @emitRuntime@ calls these with its own emitters; what
-- only one target has (host I/O, sockets, RISC-V printing and traps) stays there.
module Keel.Runtime (alloc, dropBlock, freeBlock, arenaOpen, arenaClose) where

import Control.Monad (when)
import Keel.Asm
import Keel.Lower (arrayLayout, fieldLayouts)

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
  addScaled a (T 2) (T 1) (A 0) (wordShift a)
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
  addScaled a (T 2) (T 1) (T 2) (wordShift a)
  jump a pop
  where
    bump = local a "alloc_bump"
    pop = local a "alloc_pop"
    header = local a "alloc_header"
    link0 = local a "alloc_link0"

-- | _keel_drop: A 0 = block. Decrement; at zero, drop the children and free the block. The
-- last pointer child is handled by looping, so dropping a long list uses constant stack.
-- Slots: the block, the map still to drop, its packed bit. Header (spec/memory.md): bits 0–9
-- layout, 10–30 count, 31 immortal; 32–39 words, 40–55 pointer map, 56 packed.
dropBlock :: Monad m => Asm m -> m ()
dropBlock a = do
  fn a "_keel_drop"
  frame a 3
  label a top
  load a (Half32 True) (T 0) (A 0) (-8)
  branch a Lts (T 0) (I 0) done -- immortal
  op a Shr (T 1) (T 0) (I 10)
  branch a Eq (T 1) (I 0) "_keel_panic_rc" -- the count was 0: a freed block
  op a Sub (T 0) (T 0) (I 1024)
  store a (Half32 False) (T 0) (A 0) (-8)
  op a Shr (T 1) (T 0) (I 10)
  branch a Ne (T 1) (I 0) done
  loadSym a (T 1) "_keel_arena_base"
  branch a Geu (A 0) (R (T 1)) done -- in an open arena: freed when it closes
  stat a 24 (T 1) (T 2)
  store a Word (A 0) Sp (slot a 0)
  op a And (T 2) (T 0) (I 0x3ff) -- the layout
  mov a (T 1) (I arrayLayout)
  branch a Geu (T 2) (R (T 1)) special
  headerMap a (T 0) (A 0)
  label a split
  splitPacked a (T 0) (T 1)
  label a loop
  branch a Eq (T 0) (I 0) free
  op a Sub (T 1) (T 0) (I 1)
  op a And (T 1) (T 1) (R (T 0)) -- the map without its lowest bit
  branch a Eq (T 1) (I 0) lastChild
  lowBit a (T 2) (T 0) (T 3)
  store a Word (T 1) Sp (slot a 1)
  load a Word (T 4) Sp (slot a 0)
  child a (A 0) (T 4) (T 2) (T 3)
  call a "_keel_drop"
  load a Word (T 0) Sp (slot a 1)
  jump a loop
  -- The last pointer child: free the block, then loop on the child instead of recursing.
  label a lastChild
  lowBit a (T 2) (T 0) (T 3)
  load a Word (T 4) Sp (slot a 0)
  child a (T 5) (T 4) (T 2) (T 3)
  store a Word (T 5) Sp (slot a 1)
  mov a (A 0) (R (T 4))
  call a "_keel_free_block"
  load a Word (A 0) Sp (slot a 1)
  jump a top
  label a free
  load a Word (A 0) Sp (slot a 0)
  call a "_keel_free_block"
  label a done
  unframe a 3
  ret a
  -- A block with a field in its header: its pointer map is in the table.
  label a special
  mov a (T 1) (I fieldLayouts)
  branch a Ltu (T 2) (R (T 1)) array
  op a Sub (T 2) (T 2) (I fieldLayouts)
  addr a (T 1) "_keel_layouts"
  addScaled a (T 3) (T 1) (T 2) 2
  load a (Half32 False) (T 0) (T 3) 0
  op a Shr (T 0) (T 0) (I 8)
  jump a split
  -- An array: drop its elements if they are pointers, last first, then free it.
  label a array
  mov a (T 1) (I (arrayLayout + 2))
  branch a Ne (T 2) (R (T 1)) free
  load a Word (T 0) (A 0) 0
  label a elems
  branch a Eq (T 0) (I 0) free
  op a Sub (T 0) (T 0) (I 1)
  store a Word (T 0) Sp (slot a 1)
  load a Word (T 4) Sp (slot a 0)
  addScaled a (T 1) (T 4) (T 0) (wordShift a)
  load a Word (A 0) (T 1) (2 * wordBytes a)
  call a "_keel_drop"
  load a Word (T 0) Sp (slot a 1)
  jump a elems
  where
    top = local a "drop_top"
    done = local a "drop_ret"
    split = local a "drop_split"
    loop = local a "drop_loop"
    lastChild = local a "drop_last"
    free = local a "drop_free"
    special = local a "drop_special"
    array = local a "drop_array"
    elems = local a "drop_elems"

-- | The pointer map and packed bit of the block in @b@ (its header's bits 40–56, the high
-- half's bits 8–24) into @d@.
headerMap :: Monad m => Asm m -> Reg -> Reg -> m ()
headerMap a d b = do
  load a (Half32 False) d b (-4)
  op a Shl d d (I (xlen a - 25))
  op a Shr d d (I (xlen a - 17))

-- | Split a 17-bit map in @r@: its packed bit to slot 2, @r@ the 16-bit map (uses @t@).
splitPacked :: Monad m => Asm m -> Reg -> Reg -> m ()
splitPacked a r t = do
  op a Shr t r (I 16)
  store a Word t Sp (slot a 2)
  op a Shl r r (I (xlen a - 16))
  op a Shr r r (I (xlen a - 16))

-- | Child @i@ (a map bit's index) of the block in @base@ into @d@ (≠ base): word i, or with the
-- packed bit in slot 2, 4-byte slot i holding (child - block) / 8. Uses @t@.
child :: Monad m => Asm m -> Reg -> Reg -> Reg -> Reg -> m ()
child a d base i t = do
  lPacked <- newLabel a
  lDone <- newLabel a
  load a Word t Sp (slot a 2)
  branch a Ne t (I 0) lPacked
  loadIx a d base i (wordShift a)
  jump a lDone
  label a lPacked
  addScaled a t base i 2
  load a (Half32 True) d t 0
  addScaled a d base d 3
  label a lDone

xlen :: Asm m -> Integer
xlen a = 8 * toInteger (wordBytes a)

wordShift :: Asm m -> Int
wordShift a = if wordBytes a == 4 then 2 else 3

-- | _keel_free_block: A 0 = block with count 0 → pushed on its size's free list. Clobbers T 0–3.
freeBlock :: Monad m => Asm m -> Integer -> m ()
freeBlock a maxSmall = do
  fn a "_keel_free_block"
  load a Byte (T 0) (A 0) (-4) -- its words (an array's: capped at 255)
  load a (Half32 False) (T 1) (A 0) (-8)
  branchBit a False fieldBit (T 1) (T 2) size -- the header holds a field: its size is in the table
  op a And (T 1) (T 1) (I (fieldLayouts - 1))
  addr a (T 2) "_keel_layouts"
  addScaled a (T 3) (T 2) (T 1) 2
  load a Byte (T 0) (T 3) 0
  label a size
  mov a (T 1) (I maxSmall)
  branch a Gtu (T 0) (R (T 1)) done -- ponytail: large blocks are not recycled
  addr a (T 1) "_keel_freelists"
  loadIx a (T 2) (T 1) (T 0) 3
  branch a Eq (T 0) (I 0) link0
  store a Word (T 2) (A 0) 0 -- the link, in the first word
  storeIx a (A 0) (T 1) (T 0) 3 (T 3)
  label a done
  ret a
  -- A block of no words: the link in its header's high half, in words from it (0: none).
  label a link0
  branch a Eq (T 2) (I 0) link
  op a Sub (T 2) (T 2) (R (A 0))
  op a Sar (T 2) (T 2) (I (if wordBytes a == 4 then 2 else 3))
  label a link
  store a (Half32 False) (T 2) (A 0) (-4)
  store a Word (A 0) (T 1) 0
  ret a
  where
    fieldBit = length (takeWhile (< fieldLayouts) (iterate (* 2) 1)) -- fieldLayouts = 2 ^ fieldBit
    size = local a "free_size"
    done = local a "free_ret"
    link0 = local a "free_link0"
    link = local a "free_link"

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
