-- | The runtime routines the three back ends share, written once against "Keel.Asm"
-- (spec/backends.md). Each back end's @emitRuntime@ calls these with its own emitters; what
-- only one target has (host I/O, sockets, RISC-V printing and traps) stays there.
module Keel.Runtime (alloc, dropBlock, dropReuse, freeBlock, arenaOpen, arenaClose, arrays) where

import Control.Monad (unless, when)
import Keel.Asm
import Keel.Lower (arrayLayout, fieldLayouts)

-- | The array routines. Payload [length, capacity, elements…]; the layout is arrayLayout plus
-- the kind: 0 for 4-byte elements, 1 for 8-byte ones, 2 for pointers. On RV32 a kind-1
-- element is two words, its high half in the next argument register. The header's size field
-- is capacity + 2 words, capped at 255 (larger blocks are never recycled anyway). An update
-- to an array nothing else references happens in place; otherwise the array is copied first.
arrays :: Monad m => Asm m -> m ()
arrays a = do
  arrayAlloc a
  arrayNew a
  arrayClone a
  arraySet a
  arrayPush a
  arrayPop a

-- | _keel_array_alloc: A 0 = capacity, A 1 = kind → A 0 = an empty array.
arrayAlloc :: Monad m => Asm m -> m ()
arrayAlloc a = do
  fn a "_keel_array_alloc"
  frame a 3
  store a Word (A 0) Sp (slot a 0)
  store a Word (A 1) Sp (slot a 1)
  elemWords a (A 0) (A 0) (A 1) (T 0)
  store a Word (A 0) Sp (slot a 2)
  mov a (A 1) (I 0)
  call a "_keel_alloc"
  load a Word (T 0) Sp (slot a 0)
  load a Word (T 1) Sp (slot a 1)
  mov a (T 2) (I (1024 + arrayLayout)) -- count 1, the kind's layout
  op a Add (T 2) (T 2) (R (T 1))
  store a (Half32 False) (T 2) (A 0) (-8)
  load a Word (T 3) Sp (slot a 2) -- its words, capped at 255
  capWords a (T 3) (T 4)
  store a (Half32 False) (T 3) (A 0) (-4)
  mov a (T 4) (I 0)
  store a Word (T 4) (A 0) 0
  store a Word (T 0) (A 0) (wordBytes a)
  unframe a 3
  ret a

-- | _keel_array_new: A 0 = length, A 1 = the element (owned), A 2 = kind → A 0.
arrayNew :: Monad m => Asm m -> m ()
arrayNew a = do
  fn a "_keel_array_new"
  frame a 4
  branch a Lts (A 0) (I 0) "_keel_panic_bounds"
  store a Word (A 1) Sp (slot a 0)
  store a Word (A 2) Sp (slot a 1)
  store a Word (A 0) Sp (slot a 2)
  when rv32 $ store a Word (A 3) Sp (slot a 3) -- an 8-byte element's high half
  mov a (A 1) (R (A 2))
  call a "_keel_array_alloc"
  load a Word (T 0) Sp (slot a 2)
  load a Word (T 1) Sp (slot a 0)
  load a Word (T 2) Sp (slot a 1)
  store a Word (T 0) (A 0) 0
  mov a (T 3) (I 0)
  branch a Eq (T 2) (I 0) fill4
  when rv32 $ op a Sub (T 4) (T 2) (I 1) >> branch a Eq (T 4) (I 0) fill8
  label a fill
  branch a Geu (T 3) (R (T 0)) filled
  addScaled a (T 4) (A 0) (T 3) (wordShift a)
  store a Word (T 1) (T 4) elems
  op a Add (T 3) (T 3) (I 1)
  jump a fill
  label a fill4
  branch a Geu (T 3) (R (T 0)) filled
  addScaled a (T 4) (A 0) (T 3) 2
  store a (Half32 False) (T 1) (T 4) elems
  op a Add (T 3) (T 3) (I 1)
  jump a fill4
  when rv32 $ do
    label a fill8
    load a Word (T 5) Sp (slot a 3)
    label a fill8Loop
    branch a Geu (T 3) (R (T 0)) filled
    addScaled a (T 4) (A 0) (T 3) 3
    store a Word (T 1) (T 4) 8
    store a Word (T 5) (T 4) 12
    op a Add (T 3) (T 3) (I 1)
    jump a fill8Loop
  label a filled
  mov a (T 4) (I 2)
  branch a Ne (T 2) (R (T 4)) done
  -- The element now has n references in the array; the caller gave one.
  branch a Eq (T 0) (I 0) dropIt
  load a (Half32 True) (T 4) (T 1) (-8)
  branch a Lts (T 4) (I 0) done
  op a Shr (T 5) (T 4) (I 10) -- the count
  op a Add (T 5) (T 5) (R (T 0))
  op a Sub (T 5) (T 5) (I 1)
  op a And (T 4) (T 4) (I 0x3ff)
  op a Shr (T 3) (T 5) (I 21)
  branch a Eq (T 3) (I 0) counted
  mov a (T 5) (I 0x200000) -- overflowed: immortal (bit 31 after the shift)
  label a counted
  op a Shl (T 5) (T 5) (I 10)
  op a Or (T 4) (T 4) (R (T 5))
  store a (Half32 False) (T 4) (T 1) (-8)
  jump a done
  label a dropIt
  store a Word (A 0) Sp (slot a 2)
  mov a (A 0) (R (T 1))
  call a "_keel_drop"
  load a Word (A 0) Sp (slot a 2)
  label a done
  unframe a 4
  ret a
  where
    rv32 = wordBytes a == 4
    elems = 2 * wordBytes a
    fill = local a "anew_fill"
    fill4 = local a "anew_fill4"
    fill8 = local a "anew_fill8"
    fill8Loop = local a "anew_fill8_loop"
    filled = local a "anew_filled"
    counted = local a "anew_count"
    dropIt = local a "anew_drop"
    done = local a "anew_ret"

-- | _keel_array_clone: A 0 = array (owned), A 1 = capacity ≥ its length → A 0 = a fresh array
-- with the same elements. A unique array's elements move and its block is freed; a shared
-- one's are duplicated and its count decremented.
arrayClone :: Monad m => Asm m -> m ()
arrayClone a = do
  fn a "_keel_array_clone"
  frame a 3
  store a Word (A 0) Sp (slot a 0)
  kindOf a (T 0) (A 0)
  store a Word (T 0) Sp (slot a 1)
  mov a (A 0) (R (A 1))
  mov a (A 1) (R (T 0))
  call a "_keel_array_alloc"
  load a Word (T 0) Sp (slot a 0)
  load a Word (T 1) (T 0) 0
  store a Word (T 1) (A 0) 0
  -- Copy the elements' words.
  load a Word (T 2) Sp (slot a 1)
  elemWords a (T 5) (T 1) (T 2) (T 3)
  op a Sub (T 5) (T 5) (I 2)
  mov a (T 2) (I 0)
  label a copy
  branch a Geu (T 2) (R (T 5)) copied
  addScaled a (T 3) (T 0) (T 2) (wordShift a)
  load a Word (T 4) (T 3) elems
  addScaled a (T 3) (A 0) (T 2) (wordShift a)
  store a Word (T 4) (T 3) elems
  op a Add (T 2) (T 2) (I 1)
  jump a copy
  label a copied
  load a (Half32 False) (T 2) (T 0) (-8)
  op a Shr (T 3) (T 2) (I 10)
  op a Sub (T 3) (T 3) (I 1)
  branch a Ne (T 3) (I 0) shared
  op a And (T 3) (T 2) (I 0x3ff) -- count 0
  store a (Half32 False) (T 3) (T 0) (-8)
  loadSym a (T 3) "_keel_arena_base"
  branch a Geu (T 0) (R (T 3)) done -- in an open arena: freed when it closes
  stat a 24 (T 3) (T 4)
  store a Word (A 0) Sp (slot a 1)
  mov a (A 0) (R (T 0))
  call a "_keel_free_block"
  load a Word (A 0) Sp (slot a 1)
  jump a done
  label a shared
  op a And (T 3) (T 2) (I 0x3ff)
  mov a (T 4) (I (arrayLayout + 2))
  branch a Ne (T 3) (R (T 4)) dec
  mov a (T 3) (I 0)
  label a dup
  branch a Geu (T 3) (R (T 1)) dec
  addScaled a (T 4) (T 0) (T 3) (wordShift a)
  load a Word (T 4) (T 4) elems
  load a (Half32 True) (T 5) (T 4) (-8)
  branch a Lts (T 5) (I 0) next
  op a Add (T 5) (T 5) (I 1024)
  store a (Half32 False) (T 5) (T 4) (-8)
  label a next
  op a Add (T 3) (T 3) (I 1)
  jump a dup
  label a dec
  op a Sub (T 2) (T 2) (I 1024)
  store a (Half32 False) (T 2) (T 0) (-8)
  label a done
  unframe a 3
  ret a
  where
    elems = 2 * wordBytes a
    copy = local a "aclone_copy"
    copied = local a "aclone_copied"
    shared = local a "aclone_shared"
    dup = local a "aclone_dup"
    next = local a "aclone_next"
    dec = local a "aclone_dec"
    done = local a "aclone_ret"

-- | _keel_array_set: A 0 = array (owned), A 1 = index, A 2 = element (owned) → A 0.
arraySet :: Monad m => Asm m -> m ()
arraySet a = do
  fn a "_keel_array_set"
  frame a 3
  load a Word (T 0) (A 0) 0
  branch a Geu (A 1) (R (T 0)) "_keel_panic_bounds"
  unique a (T 1) (A 0) put
  store a Word (A 1) Sp (slot a 0)
  store a Word (A 2) Sp (slot a 1)
  when rv32 $ store a Word (A 3) Sp (slot a 2)
  load a Word (A 1) (A 0) (wordBytes a)
  call a "_keel_array_clone"
  load a Word (A 1) Sp (slot a 0)
  load a Word (A 2) Sp (slot a 1)
  when rv32 $ load a Word (A 3) Sp (slot a 2)
  label a put
  kindOf a (T 2) (A 0)
  branch a Ne (T 2) (I 0) word
  addScaled a (T 0) (A 0) (A 1) 2
  store a (Half32 False) (A 2) (T 0) elems
  jump a done
  label a word
  when rv32 $ do -- 8-byte elements (kind 1) in A 2, A 3
    op a Sub (T 4) (T 2) (I 1)
    branch a Ne (T 4) (I 0) word4
    addScaled a (T 0) (A 0) (A 1) 3
    store a Word (A 2) (T 0) 8
    store a Word (A 3) (T 0) 12
    jump a done
    label a word4
  addScaled a (T 0) (A 0) (A 1) (wordShift a)
  load a Word (T 1) (T 0) elems
  store a Word (A 2) (T 0) elems
  op a Sub (T 2) (T 2) (I 2)
  branch a Ne (T 2) (I 0) done
  store a Word (A 0) Sp (slot a 0)
  mov a (A 0) (R (T 1))
  call a "_keel_drop" -- the element it replaced
  load a Word (A 0) Sp (slot a 0)
  label a done
  unframe a 3
  ret a
  where
    rv32 = wordBytes a == 4
    elems = 2 * wordBytes a
    put = local a "aset_store"
    word = local a "aset_word"
    word4 = local a "aset_w4"
    done = local a "aset_ret"

-- | _keel_array_push: A 0 = array (owned), A 1 = element (owned; on RV32 an 8-byte one's high
-- half in A 2) → A 0. A full array doubles: in place when it is unique and the last block
-- before the bump pointer (then nothing lies after it, not even an arena's record), otherwise
-- into a copy.
arrayPush :: Monad m => Asm m -> m ()
arrayPush a = do
  fn a "_keel_array_push"
  frame a 2
  store a Word (A 1) Sp (slot a 0)
  when rv32 $ store a Word (A 2) Sp (slot a 1)
  load a Word (T 0) (A 0) 0
  load a Word (T 1) (A 0) (wordBytes a)
  branch a Geu (T 0) (R (T 1)) grow
  unique a (T 2) (A 0) put
  mov a (A 1) (R (T 1))
  call a "_keel_array_clone"
  jump a put
  label a grow
  op a Shl (A 1) (T 1) (I 1)
  mov a (T 3) (I 4)
  branch a Geu (A 1) (R (T 3)) capped
  mov a (A 1) (R (T 3))
  label a capped
  unique a (T 2) (A 0) inPlace
  jump a copy
  label a inPlace
  kindOf a (T 2) (A 0)
  elemWords a (T 4) (T 1) (T 2) (T 3)
  addScaled a (T 4) (A 0) (T 4) (wordShift a) -- the block's end
  addr a (T 5) "_keel_heap_ptr"
  load a Word (T 3) (T 5) 0
  branch a Ne (T 4) (R (T 3)) copy
  elemWords a (T 4) (A 1) (T 2) (T 3)
  addScaled a (T 3) (A 0) (T 4) (wordShift a)
  load a Word (T 1) (T 5) 8
  branch a Gtu (T 3) (R (T 1)) "_keel_panic_oom"
  store a Word (T 3) (T 5) 0
  store a Word (A 1) (A 0) (wordBytes a)
  capWords a (T 4) (T 1) -- the header's words, capped as in _keel_array_alloc
  store a Byte (T 4) (A 0) (-4)
  jump a put
  label a copy
  call a "_keel_array_clone"
  label a put
  load a Word (T 0) (A 0) 0
  load a Word (A 1) Sp (slot a 0)
  kindOf a (T 2) (A 0)
  branch a Ne (T 2) (I 0) word
  addScaled a (T 1) (A 0) (T 0) 2
  store a (Half32 False) (A 1) (T 1) elems
  jump a count
  label a word
  when rv32 $ do -- 8-byte elements (kind 1), the high half in slot 1
    op a Sub (T 4) (T 2) (I 1)
    branch a Ne (T 4) (I 0) word4
    addScaled a (T 1) (A 0) (T 0) 3
    store a Word (A 1) (T 1) 8
    load a Word (T 3) Sp (slot a 1)
    store a Word (T 3) (T 1) 12
    jump a count
    label a word4
  addScaled a (T 1) (A 0) (T 0) (wordShift a)
  store a Word (A 1) (T 1) elems
  label a count
  op a Add (T 0) (T 0) (I 1)
  store a Word (T 0) (A 0) 0
  unframe a 2
  ret a
  where
    rv32 = wordBytes a == 4
    elems = 2 * wordBytes a
    grow = local a "apush_grow"
    capped = local a "apush_cap"
    inPlace = local a "apush_in_place"
    copy = local a "apush_copy"
    put = local a "apush_store"
    word = local a "apush_word"
    word4 = local a "apush_w4"
    count = local a "apush_count"

-- | _keel_array_pop: A 0 = array (owned) → A 0 without its last element.
arrayPop :: Monad m => Asm m -> m ()
arrayPop a = do
  fn a "_keel_array_pop"
  frame a 1
  load a Word (T 0) (A 0) 0
  branch a Eq (T 0) (I 0) "_keel_panic_bounds"
  unique a (T 1) (A 0) takeLast
  load a Word (A 1) (A 0) (wordBytes a)
  call a "_keel_array_clone"
  label a takeLast
  load a Word (T 0) (A 0) 0
  op a Sub (T 0) (T 0) (I 1)
  store a Word (T 0) (A 0) 0
  kindOf a (T 2) (A 0)
  mov a (T 3) (I 2)
  branch a Ne (T 2) (R (T 3)) done
  addScaled a (T 1) (A 0) (T 0) (wordShift a)
  store a Word (A 0) Sp (slot a 0)
  load a Word (A 0) (T 1) (2 * wordBytes a)
  call a "_keel_drop"
  load a Word (A 0) Sp (slot a 0)
  label a done
  unframe a 1
  ret a
  where
    takeLast = local a "apop_take"
    done = local a "apop_ret"

-- | The kind of the array in @b@ into @d@.
kindOf :: Monad m => Asm m -> Reg -> Reg -> m ()
kindOf a d b = do
  load a (Half32 False) d b (-8)
  op a And d d (I 0x3ff)
  op a Sub d d (I arrayLayout)

-- | To @l@ when the block in @b@ has a count of exactly 1 (uses @t@).
unique :: Monad m => Asm m -> Reg -> Reg -> String -> m ()
unique a t b l = do
  load a (Half32 False) t b (-8)
  op a Shr t t (I 10)
  op a Sub t t (I 1)
  branch a Eq t (I 0) l

-- | An array's payload words for @n@ elements of kind @k@ into @d@ (≠ k): 2 + the elements,
-- rounded up to words. Uses @t@ on RV32.
elemWords :: Monad m => Asm m -> Reg -> Reg -> Reg -> Reg -> m ()
elemWords a d n k t = do
  lOther <- newLabel a
  lAdd <- newLabel a
  if wordBytes a == 4
    then do -- a word per element, two for kind 1
      op a Sub t k (I 1)
      branch a Ne t (I 0) lOther
      op a Shl d n (I 1)
      jump a lAdd
      label a lOther
      unless (d == n) $ mov a d (R n)
      label a lAdd
      op a Add d d (I 2)
    else do -- 4-byte elements for kind 0, 8-byte ones otherwise
      branch a Eq k (I 0) lOther
      op a Shl d n (I 3)
      jump a lAdd
      label a lOther
      op a Shl d n (I 2)
      label a lAdd
      op a Add d d (I 23) -- + 7 to round up, + 16 for length and capacity
      op a Shr d d (I 3)

-- | Cap the words in @r@ at 255, the header's size field (uses @t@).
capWords :: Monad m => Asm m -> Reg -> Reg -> m ()
capWords a r t = do
  lOk <- newLabel a
  mov a t (I 0xFF)
  branch a Ltu r (R t) lOk
  mov a r (R t)
  label a lOk

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

-- | _keel_drop_reuse: A 0 = block, A 1 = the fields taken over (a mask of words) → A 0 = the
-- block if it was unique (its other children dropped, count 0 until reused), or 0 after an
-- ordinary decrement and duplicating the fields taken over. Slots as in 'dropBlock'.
dropReuse :: Monad m => Asm m -> m ()
dropReuse a = do
  fn a "_keel_drop_reuse"
  frame a 3
  load a (Half32 True) (T 0) (A 0) (-8)
  branch a Lts (T 0) (I 0) none -- immortal
  op a Shr (T 1) (T 0) (I 10)
  branch a Eq (T 1) (I 0) "_keel_panic_rc"
  op a Sub (T 1) (T 1) (I 1)
  branch a Ne (T 1) (I 0) shared
  stat a 24 (T 1) (T 2)
  store a Word (A 0) Sp (slot a 0)
  reuseMap a (T 0) (A 0)
  op a And (T 1) (T 0) (R (A 1)) -- the fields taken over stay alive: they are the caller's now
  op a Xor (T 0) (T 0) (R (T 1))
  label a loop
  branch a Eq (T 0) (I 0) dropped
  op a Sub (T 1) (T 0) (I 1)
  op a And (T 1) (T 1) (R (T 0))
  lowBit a (T 2) (T 0) (T 3)
  store a Word (T 1) Sp (slot a 1)
  load a Word (T 4) Sp (slot a 0)
  child a (A 0) (T 4) (T 2) (T 3)
  call a "_keel_drop"
  load a Word (T 0) Sp (slot a 1)
  jump a loop
  label a dropped
  load a Word (A 0) Sp (slot a 0)
  load a (Half32 False) (T 0) (A 0) (-8)
  op a And (T 0) (T 0) (I 0x3ff) -- count 0 until reused
  store a (Half32 False) (T 0) (A 0) (-8)
  jump a done
  label a shared
  op a Sub (T 0) (T 0) (I 1024)
  store a (Half32 False) (T 0) (A 0) (-8)
  -- The block keeps its references: duplicate the fields taken over.
  label a none
  branch a Eq (A 1) (I 0) zero
  reuseMap a (T 0) (A 0) -- only for its packed bit
  label a dup
  lowBit a (T 2) (A 1) (T 3)
  op a Sub (T 1) (A 1) (I 1)
  op a And (A 1) (A 1) (R (T 1))
  child a (T 4) (A 0) (T 2) (T 3)
  load a (Half32 True) (T 5) (T 4) (-8)
  branch a Lts (T 5) (I 0) next
  op a Add (T 5) (T 5) (I 1024)
  store a (Half32 False) (T 5) (T 4) (-8)
  label a next
  branch a Ne (A 1) (I 0) dup
  label a zero
  mov a (A 0) (I 0)
  label a done
  unframe a 3
  ret a
  where
    shared = local a "reuse_shared"
    none = local a "reuse_none"
    loop = local a "reuse_loop"
    dropped = local a "reuse_done"
    dup = local a "reuse_dup"
    next = local a "reuse_next"
    zero = local a "reuse_zero"
    done = local a "reuse_ret"

-- | The map of the block in @b@ into @d@ (from the layout table when its header holds a
-- field), its packed bit to slot 2. Uses T 1–3.
reuseMap :: Monad m => Asm m -> Reg -> Reg -> m ()
reuseMap a d b = do
  lMap <- newLabel a
  headerMap a d b
  load a (Half32 False) (T 1) b (-8)
  branchBit a False fieldBit (T 1) (T 2) lMap
  op a And (T 1) (T 1) (I (fieldLayouts - 1))
  addr a (T 2) "_keel_layouts"
  addScaled a (T 3) (T 2) (T 1) 2
  load a (Half32 False) d (T 3) 0
  op a Shr d d (I 8)
  label a lMap
  splitPacked a d (T 1)

-- | fieldLayouts = 2 ^ fieldBit: the header bit that says it holds a field.
fieldBit :: Int
fieldBit = length (takeWhile (< fieldLayouts) (iterate (* 2) 1))

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
