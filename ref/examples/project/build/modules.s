	.section __TEXT,__text,regular,pure_instructions
	.p2align 2
_kf_0:			// greet
	stp x29, x30, [sp, #-16]!
	mov x29, sp
	sub sp, sp, #128
	str x19, [sp, #48]
	str x20, [sp, #56]
	str x21, [sp, #64]
	str x22, [sp, #72]
	str x23, [sp, #80]
	str x24, [sp, #88]
	str x25, [sp, #96]
	str x26, [sp, #104]
	str x27, [sp, #112]
	str x28, [sp, #120]
	mov x19, x1
	movz x0, #1
	mov x1, #0
	bl _keel_alloc
	mov x11, #0
	str x11, [x0]
	mov x20, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #32
	str x11, [x0, #8]
	mov x11, x20
	str x11, [x0, #16]
	mov x21, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #44
	str x11, [x0, #8]
	mov x11, x21
	str x11, [x0, #16]
	mov x22, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #111
	str x11, [x0, #8]
	mov x11, x22
	str x11, [x0, #16]
	mov x23, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #108
	str x11, [x0, #8]
	mov x11, x23
	str x11, [x0, #16]
	mov x24, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #108
	str x11, [x0, #8]
	mov x11, x24
	str x11, [x0, #16]
	mov x25, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #101
	str x11, [x0, #8]
	mov x11, x25
	str x11, [x0, #16]
	mov x26, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #104
	str x11, [x0, #8]
	mov x11, x26
	str x11, [x0, #16]
	mov x27, x0
	mov x0, x27
	mov x28, x0
	mov x1, x28
	bl _kf_1
	str x0, [sp, #0]
	ldr x0, [sp, #0]
	str x0, [sp, #8]
	mov x0, x19
	str x0, [sp, #16]
	ldr x1, [sp, #16]
	bl _kf_1
	str x0, [sp, #24]
	ldr x0, [sp, #24]
	str x0, [sp, #32]
	movz x1, #10
	movz x0, #1
	bl _keel_perform
	str x0, [sp, #40]
	ldr x0, [sp, #40]
	ldr x19, [sp, #48]
	ldr x20, [sp, #56]
	ldr x21, [sp, #64]
	ldr x22, [sp, #72]
	ldr x23, [sp, #80]
	ldr x24, [sp, #88]
	ldr x25, [sp, #96]
	ldr x26, [sp, #104]
	ldr x27, [sp, #112]
	ldr x28, [sp, #120]
	mov sp, x29
	ldp x29, x30, [sp], #16
	ret
	.p2align 2
_kf_1:			// print
	stp x29, x30, [sp, #-16]!
	mov x29, sp
	sub sp, sp, #64
	str x19, [sp, #0]
	str x20, [sp, #8]
	str x21, [sp, #16]
	str x22, [sp, #24]
	str x23, [sp, #32]
	str x24, [sp, #40]
	str x25, [sp, #48]
	mov x19, x1
	mov x9, x19
	ldr x9, [x9]
	cmp x9, #0
	b.eq Lk1
	b Lk2
Lk1:
	mov x0, x19
	bl _keel_drop
	mov x0, #0
	ldr x19, [sp, #0]
	ldr x20, [sp, #8]
	ldr x21, [sp, #16]
	ldr x22, [sp, #24]
	ldr x23, [sp, #32]
	ldr x24, [sp, #40]
	ldr x25, [sp, #48]
	mov sp, x29
	ldp x29, x30, [sp], #16
	ret
Lk2:
	mov x9, x19
	ldr x0, [x9, #8]
	mov x22, x0
	mov x9, x19
	ldr x0, [x9, #16]
	mov x20, x0
	mov x16, x20
	ldr w17, [x16, #-8]
	tbnz w17, #31, Lk3
	cbz w17, _keel_panic_rc
	add w17, w17, #1
	str w17, [x16, #-8]
Lk3:
	mov x0, x19
	bl _keel_drop
	mov x1, x22
	movz x0, #1
	bl _keel_perform
	mov x23, x0
	mov x0, x23
	mov x25, x0
	mov x1, x20
	ldr x19, [sp, #0]
	ldr x20, [sp, #8]
	ldr x21, [sp, #16]
	ldr x22, [sp, #24]
	ldr x23, [sp, #32]
	ldr x24, [sp, #40]
	ldr x25, [sp, #48]
	mov sp, x29
	ldp x29, x30, [sp], #16
	b _kf_1
	.p2align 2
_kf_2:			// printU64
	stp x29, x30, [sp, #-16]!
	mov x29, sp
	sub sp, sp, #112
	str x19, [sp, #24]
	str x20, [sp, #32]
	str x21, [sp, #40]
	str x22, [sp, #48]
	str x23, [sp, #56]
	str x24, [sp, #64]
	str x25, [sp, #72]
	str x26, [sp, #80]
	str x27, [sp, #88]
	str x28, [sp, #96]
	mov x19, x1
	mov x9, x19
	movz x10, #10
	cmp x9, x10
	cset x0, lo
	mov x20, x0
	mov x9, x20
	cbz x9, Lk4
	mov x9, x19
	movz x10, #48
	adds x0, x9, x10
	b.cs _keel_panic_overflow
	mov x22, x0
	mov x0, x22
	and x0, x0, #255
	mov x23, x0
	mov x1, x23
	movz x0, #1
	bl _keel_perform
	mov x24, x0
	mov x0, x24
	ldr x19, [sp, #24]
	ldr x20, [sp, #32]
	ldr x21, [sp, #40]
	ldr x22, [sp, #48]
	ldr x23, [sp, #56]
	ldr x24, [sp, #64]
	ldr x25, [sp, #72]
	ldr x26, [sp, #80]
	ldr x27, [sp, #88]
	ldr x28, [sp, #96]
	mov sp, x29
	ldp x29, x30, [sp], #16
	ret
Lk4:
	mov x9, x19
	movz x10, #10
	cbz x10, _keel_panic_div
	udiv x0, x9, x10
	mov x25, x0
	mov x1, x25
	bl _kf_2
	mov x26, x0
	mov x0, x26
	str x0, [sp, #0]
	mov x9, x19
	movz x10, #10
	cbz x10, _keel_panic_div
	udiv x11, x9, x10
	msub x0, x11, x10, x9
	mov x27, x0
	mov x9, x27
	movz x10, #48
	adds x0, x9, x10
	b.cs _keel_panic_overflow
	mov x28, x0
	mov x0, x28
	and x0, x0, #255
	str x0, [sp, #8]
	ldr x1, [sp, #8]
	movz x0, #1
	bl _keel_perform
	str x0, [sp, #16]
	ldr x0, [sp, #16]
	ldr x19, [sp, #24]
	ldr x20, [sp, #32]
	ldr x21, [sp, #40]
	ldr x22, [sp, #48]
	ldr x23, [sp, #56]
	ldr x24, [sp, #64]
	ldr x25, [sp, #72]
	ldr x26, [sp, #80]
	ldr x27, [sp, #88]
	ldr x28, [sp, #96]
	mov sp, x29
	ldp x29, x30, [sp], #16
	ret
	.p2align 2
_kf_main:			// main
	stp x29, x30, [sp, #-16]!
	mov x29, sp
	sub sp, sp, #272
	str x19, [sp, #184]
	str x20, [sp, #192]
	str x21, [sp, #200]
	str x22, [sp, #208]
	str x23, [sp, #216]
	str x24, [sp, #224]
	str x25, [sp, #232]
	str x26, [sp, #240]
	str x27, [sp, #248]
	str x28, [sp, #256]
	movz x0, #1
	mov x1, #0
	bl _keel_alloc
	mov x11, #0
	str x11, [x0]
	mov x22, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #115
	str x11, [x0, #8]
	mov x11, x22
	str x11, [x0, #16]
	mov x23, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #101
	str x11, [x0, #8]
	mov x11, x23
	str x11, [x0, #16]
	mov x24, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #108
	str x11, [x0, #8]
	mov x11, x24
	str x11, [x0, #16]
	mov x25, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #117
	str x11, [x0, #8]
	mov x11, x25
	str x11, [x0, #16]
	mov x26, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #100
	str x11, [x0, #8]
	mov x11, x26
	str x11, [x0, #16]
	mov x27, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #111
	str x11, [x0, #8]
	mov x11, x27
	str x11, [x0, #16]
	mov x28, x0
	movz x0, #3
	movz x1, #4
	bl _keel_alloc
	movz x11, #1
	str x11, [x0]
	movz x11, #109
	str x11, [x0, #8]
	mov x11, x28
	str x11, [x0, #16]
	str x0, [sp, #0]
	ldr x1, [sp, #0]
	bl _kf_0
	str x0, [sp, #8]
	ldr x0, [sp, #8]
	str x0, [sp, #16]
	movz x0, #21
	mov x20, x0
	mov x0, x20
	str x0, [sp, #24]
	mov x0, x20
	str x0, [sp, #32]
	ldr x9, [sp, #24]
	ldr x10, [sp, #32]
	adds x0, x9, x10
	b.vs _keel_panic_overflow
	str x0, [sp, #40]
	ldr x0, [sp, #40]
	mov x19, x0
	mov x9, x19
	mov x10, #0
	cmp x9, x10
	cset x0, lt
	str x0, [sp, #48]
	ldr x9, [sp, #48]
	cbz x9, Lk6
	movz x1, #45
	movz x0, #1
	bl _keel_perform
	str x0, [sp, #64]
	ldr x0, [sp, #64]
	str x0, [sp, #72]
	mov x9, x19
	movz x10, #1
	adds x0, x9, x10
	b.vs _keel_panic_overflow
	str x0, [sp, #80]
	mov x9, #0
	ldr x10, [sp, #80]
	subs x0, x9, x10
	b.vs _keel_panic_overflow
	str x0, [sp, #88]
	ldr x0, [sp, #88]
	str x0, [sp, #96]
	ldr x9, [sp, #96]
	movz x10, #1
	adds x0, x9, x10
	b.cs _keel_panic_overflow
	str x0, [sp, #104]
	ldr x1, [sp, #104]
	bl _kf_2
	str x0, [sp, #112]
	ldr x0, [sp, #112]
	str x0, [sp, #56]
	b Lk7
Lk6:
	mov x0, x19
	str x0, [sp, #120]
	ldr x1, [sp, #120]
	bl _kf_2
	str x0, [sp, #128]
	ldr x0, [sp, #128]
	str x0, [sp, #56]
	b Lk7
Lk7:
	ldr x0, [sp, #56]
	str x0, [sp, #136]
	movz x1, #10
	movz x0, #1
	bl _keel_perform
	str x0, [sp, #144]
	ldr x0, [sp, #144]
	str x0, [sp, #152]
	movz x0, #50
	mov x21, x0
	mov x0, x21
	str x0, [sp, #160]
	mov x0, x21
	str x0, [sp, #168]
	ldr x9, [sp, #160]
	ldr x10, [sp, #168]
	adds x0, x9, x10
	b.vs _keel_panic_overflow
	str x0, [sp, #176]
	ldr x0, [sp, #176]
	ldr x19, [sp, #184]
	ldr x20, [sp, #192]
	ldr x21, [sp, #200]
	ldr x22, [sp, #208]
	ldr x23, [sp, #216]
	ldr x24, [sp, #224]
	ldr x25, [sp, #232]
	ldr x26, [sp, #240]
	ldr x27, [sp, #248]
	ldr x28, [sp, #256]
	mov sp, x29
	ldp x29, x30, [sp], #16
	ret
	.globl _main
	.p2align 2
_main:
	stp x29, x30, [sp, #-16]!
	mov x29, sp
	sub sp, sp, #64
	mov x0, #0
	bl _kf_main
	str x0, [sp, #48]
	adrp x0, _keel_s0@PAGE
	add x0, x0, _keel_s0@PAGEOFF
	bl _printf
	ldr x0, [sp, #48]
	bl _kp_0
	adrp x0, _keel_s1@PAGE
	add x0, x0, _keel_s1@PAGEOFF
	bl _printf
	adrp x0, _keel_s2@PAGE
	add x0, x0, _keel_s2@PAGEOFF
	bl _getenv
	cbz x0, Lk8
	adrp x13, _keel_stats@PAGE
	add x13, x13, _keel_stats@PAGEOFF
	ldp x9, x10, [x13]
	ldp x11, x12, [x13, #16]
	stp x9, x10, [sp]
	stp x11, x12, [sp, #16]
	add x14, x9, x10
	add x14, x14, x11
	sub x14, x14, x12
	str x14, [sp, #32]
	mov x0, #2
	adrp x1, _keel_s3@PAGE
	add x1, x1, _keel_s3@PAGEOFF
	bl _dprintf
Lk8:
	mov x0, #0
	mov sp, x29
	ldp x29, x30, [sp], #16
	ret
	.p2align 2
_kp_0:			// print i64
	stp x29, x30, [sp, #-16]!
	mov x29, sp
	sub sp, sp, #32
	str x0, [sp, #16]
	str x0, [sp]
	adrp x0, _keel_s4@PAGE
	add x0, x0, _keel_s4@PAGEOFF
	bl _printf
	mov sp, x29
	ldp x29, x30, [sp], #16
	ret
	.p2align 2
_keel_alloc:
	cmp x0, #64
	b.hi L_alloc_bump
	adrp x13, _keel_freelists@PAGE
	add x13, x13, _keel_freelists@PAGEOFF
	ldr x14, [x13, x0, lsl #3]
	cbz x14, L_alloc_bump
	ldr x15, [x14]
	str x15, [x13, x0, lsl #3]
	adrp x15, _keel_stats@PAGE
	add x15, x15, _keel_stats@PAGEOFF
	ldr x16, [x15, #8]
	add x16, x16, #1
	str x16, [x15, #8]
	b L_alloc_header
L_alloc_bump:
	adrp x13, _keel_heap_ptr@PAGE
	add x13, x13, _keel_heap_ptr@PAGEOFF
	ldr x14, [x13]
	add x15, x14, x0, lsl #3
	add x15, x15, #8
	ldr x16, [x13, #8]
	cmp x15, x16
	b.hi _keel_panic_oom
	str x15, [x13]
	add x14, x14, #8
	adrp x15, _keel_stats@PAGE
	add x15, x15, _keel_stats@PAGEOFF
	ldr x16, [x15, #0]
	add x16, x16, #1
	str x16, [x15, #0]
L_alloc_header:
	lsl x15, x0, #32
	orr x15, x15, x1, lsl #48
	orr x15, x15, #1
	str x15, [x14, #-8]
	mov x0, x14
	ret
	.p2align 2
_keel_drop:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
L_drop_top:
	ldr w9, [x0, #-8]
	tbnz w9, #31, L_drop_ret
	cbz w9, _keel_panic_rc
	sub w9, w9, #1
	str w9, [x0, #-8]
	cbnz w9, L_drop_ret
	adrp x12, _keel_stats@PAGE
	add x12, x12, _keel_stats@PAGEOFF
	ldr x13, [x12, #24]
	add x13, x13, #1
	str x13, [x12, #24]
	str x0, [sp, #16]
	ldr x11, [x0, #-8]
	lsr x11, x11, #48
L_drop_loop:
	cbz x11, L_drop_free
	sub x13, x11, #1
	tst x11, x13
	b.eq L_drop_last
	rbit x13, x11
	clz x13, x13
	mov x14, #1
	lsl x14, x14, x13
	bic x11, x11, x14
	str x11, [sp, #24]
	ldr x9, [sp, #16]
	ldr x0, [x9, x13, lsl #3]
	bl _keel_drop
	ldr x11, [sp, #24]
	b L_drop_loop
L_drop_last:
	rbit x13, x11
	clz x13, x13
	ldr x0, [sp, #16]
	ldr x9, [x0, x13, lsl #3]
	str x9, [sp, #24]
	bl _keel_free_block
	ldr x0, [sp, #24]
	b L_drop_top
L_drop_free:
	ldr x0, [sp, #16]
	bl _keel_free_block
L_drop_ret:
	ldp x29, x30, [sp], #32
	ret
	.p2align 2
_keel_free_block:
	ldr x10, [x0, #-8]
	ubfx x11, x10, #32, #16
	cmp x11, #64
	b.hi L_free_ret
	adrp x12, _keel_freelists@PAGE
	add x12, x12, _keel_freelists@PAGEOFF
	ldr x13, [x12, x11, lsl #3]
	str x13, [x0]
	str x0, [x12, x11, lsl #3]
L_free_ret:
	ret
	.p2align 2
_keel_drop_reuse:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	ldr w9, [x0, #-8]
	tbnz w9, #31, L_reuse_none
	cbz w9, _keel_panic_rc
	cmp w9, #1
	b.ne L_reuse_shared
	adrp x12, _keel_stats@PAGE
	add x12, x12, _keel_stats@PAGEOFF
	ldr x13, [x12, #24]
	add x13, x13, #1
	str x13, [x12, #24]
	str x0, [sp, #16]
	ldr x11, [x0, #-8]
	lsr x11, x11, #48
L_reuse_loop:
	cbz x11, L_reuse_done
	rbit x13, x11
	clz x13, x13
	mov x14, #1
	lsl x14, x14, x13
	bic x11, x11, x14
	str x11, [sp, #24]
	ldr x9, [sp, #16]
	ldr x0, [x9, x13, lsl #3]
	bl _keel_drop
	ldr x11, [sp, #24]
	b L_reuse_loop
L_reuse_done:
	ldr x0, [sp, #16]
	str wzr, [x0, #-8]
	b L_reuse_ret
L_reuse_shared:
	sub w9, w9, #1
	str w9, [x0, #-8]
L_reuse_none:
	mov x0, #0
L_reuse_ret:
	ldp x29, x30, [sp], #32
	ret
	.p2align 2
_keel_perform:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	adrp x9, _keel_handlers@PAGE
	add x9, x9, _keel_handlers@PAGEOFF
	ldr x10, [x9]
	str x10, [sp, #16]
L_perform_frame:
	cbz x10, L_perform_machine
	ldr x11, [x10, #8]
	add x12, x10, #16
L_perform_scan:
	cbz x11, L_perform_next
	ldr x13, [x12]
	cmp x13, x0
	b.eq L_perform_found
	add x12, x12, #16
	sub x11, x11, #1
	b L_perform_scan
L_perform_next:
	ldr x10, [x10]
	b L_perform_frame
L_perform_found:
	ldr x14, [x10]
	str x14, [x9]
	ldr x0, [x12, #8]
	ldr w15, [x0, #-8]
	tbnz w15, #31, L_perform_call
	add w15, w15, #1
	str w15, [x0, #-8]
L_perform_call:
	ldr x16, [x0]
	blr x16
	ldr x10, [sp, #16]
	adrp x9, _keel_handlers@PAGE
	add x9, x9, _keel_handlers@PAGEOFF
	str x10, [x9]
	ldp x29, x30, [sp], #32
	ret
L_perform_machine:
	cmp x0, #1
	b.eq L_perform_putc
	cbnz x0, _keel_panic_unhandled
	sub sp, sp, #16
	str x1, [sp]
	adrp x0, _keel_s5@PAGE
	add x0, x0, _keel_s5@PAGEOFF
	bl _printf
	add sp, sp, #16
	mov x0, #0
	ldp x29, x30, [sp], #32
	ret
L_perform_putc:
	mov x0, x1
	bl _putchar
	mov x0, #0
	ldp x29, x30, [sp], #32
	ret
	.p2align 2
_keel_panic_unhandled:
	mov x0, #2
	adrp x1, _keel_s6@PAGE
	add x1, x1, _keel_s6@PAGEOFF
	mov x2, #62
	bl _write
	mov x0, #101
	bl _exit
	.p2align 2
_keel_panic_div:
	mov x0, #2
	adrp x1, _keel_s7@PAGE
	add x1, x1, _keel_s7@PAGEOFF
	mov x2, #24
	bl _write
	mov x0, #101
	bl _exit
	.p2align 2
_keel_panic_overflow:
	mov x0, #2
	adrp x1, _keel_s8@PAGE
	add x1, x1, _keel_s8@PAGEOFF
	mov x2, #27
	bl _write
	mov x0, #101
	bl _exit
	.p2align 2
_keel_panic_oom:
	mov x0, #2
	adrp x1, _keel_s9@PAGE
	add x1, x1, _keel_s9@PAGEOFF
	mov x2, #21
	bl _write
	mov x0, #101
	bl _exit
	.p2align 2
_keel_panic_rc:
	mov x0, #2
	adrp x1, _keel_s10@PAGE
	add x1, x1, _keel_s10@PAGEOFF
	mov x2, #29
	bl _write
	mov x0, #101
	bl _exit
	.section __DATA,__data
	.p2align 3
	.quad 0x80000000		// header: immortal
_kc_0:			// static block of greet
	.quad _kf_0
	.quad 0x80000000		// header: immortal
_kc_1:			// static block of print
	.quad _kf_1
	.quad 0x80000000		// header: immortal
_kc_2:			// static block of printU64
	.quad _kf_2
_keel_heap_ptr:
	.quad _keel_heap
	.quad _keel_heap+67108864
	.zerofill __DATA,__bss,_keel_heap,67108864,4
	.zerofill __DATA,__bss,_keel_freelists,520,3
	.zerofill __DATA,__bss,_keel_stats,32,3
	.zerofill __DATA,__bss,_keel_handlers,8,3
	.section __TEXT,__cstring,cstring_literals
_keel_s1:	.asciz "\n"
_keel_s4:	.asciz "%lld"
_keel_s5:	.asciz "%lld\n"
_keel_s2:	.asciz "KEEL_STATS"
_keel_s3:	.asciz "keel-stats: allocs=%lld recycled=%lld inplace=%lld freed=%lld live=%lld\n"
_keel_s8:	.asciz "panic: arithmetic overflow\n"
_keel_s7:	.asciz "panic: division by zero\n"
_keel_s9:	.asciz "panic: out of memory\n"
_keel_s10:	.asciz "panic: reference count error\n"
_keel_s6:	.asciz "panic: unhandled operation (MMIO needs a freestanding target)\n"
_keel_s0:	.asciz "result: "
