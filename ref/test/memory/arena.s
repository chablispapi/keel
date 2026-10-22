	.section .text.start, "ax"
	.globl _start
	.p2align 2
_start:
	la sp, _keel_stack_top
	li a0, 0
	call _kf_main
	addi sp, sp, -16
	sd a0, 0(sp)
	la a0, _keel_s0
	call _keel_print_str
	ld a0, 0(sp)
	call _kp_0
	la a0, _keel_s1
	call _keel_print_str
	la a0, _keel_s2
	call _keel_print_str
	la a0, _keel_s3
	call _keel_print_str
	la t0, _keel_stats
	ld a0, 0(t0)
	call _keel_print_u64
	la a0, _keel_s4
	call _keel_print_str
	la t0, _keel_stats
	ld a0, 8(t0)
	call _keel_print_u64
	la a0, _keel_s5
	call _keel_print_str
	la t0, _keel_stats
	ld a0, 16(t0)
	call _keel_print_u64
	la a0, _keel_s6
	call _keel_print_str
	la t0, _keel_stats
	ld a0, 24(t0)
	call _keel_print_u64
	la a0, _keel_s7
	call _keel_print_str
	la t0, _keel_stats
	ld t1, 0(t0)
	ld t2, 8(t0)
	add t1, t1, t2
	ld t2, 16(t0)
	add t1, t1, t2
	ld t2, 24(t0)
	sub a0, t1, t2
	call _keel_print_i64
	la a0, _keel_s1
	call _keel_print_str
	li a0, 0
	tail _keel_exit
	.text
	.p2align 2
_kf_0:			# check
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -64
	sd s1, 0(sp)
	sd s2, 8(sp)
	sd s3, 16(sp)
	sd s4, 24(sp)
	sd s5, 32(sp)
	sd s6, 40(sp)
	sd s7, 48(sp)
	sd s8, 56(sp)
L_kf_0_loop:
	mv s1, a1
	mv t0, s1
	lbu t0, -3(t0)
	li t1, 0
	bne t0, t1, .Lk3
	j .Lk1
.Lk3:
	j .Lk2
.Lk1:
	li a0, 1
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
.Lk2:
	mv t0, s1
	ld a0, 0(t0)
	mv s3, a0
	mv t0, s1
	ld a0, 8(t0)
	mv s4, a0
	mv a1, s3
	call _kf_0
	mv s5, a0
	li t0, 1
	mv t1, s5
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk4
	j _keel_panic_overflow
.Lk4:
	mv s6, a0
	mv a1, s4
	call _kf_0
	mv s7, a0
	mv t0, s6
	mv t1, s7
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk5
	j _keel_panic_overflow
.Lk5:
	mv s8, a0
	mv a0, s8
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_kf_1:			# make@arena
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -64
	sd s1, 0(sp)
	sd s2, 8(sp)
	sd s3, 16(sp)
	sd s4, 24(sp)
	sd s5, 32(sp)
	sd s6, 40(sp)
	sd s7, 48(sp)
	sd s8, 56(sp)
L_kf_1_loop:
	mv s1, a1
	mv t0, s1
	li t1, 0
	xor a0, t0, t1
	seqz a0, a0
	mv s2, a0
	mv t0, s2
	bnez t0, .Lk8
	j .Lk6
.Lk8:
	la a0, _kn_0
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
.Lk6:
	mv t0, s1
	li t1, 1
	sub a0, t0, t1
	xor t2, t0, t1
	xor t3, t0, a0
	and t2, t2, t3
	bgez t2, .Lk9
	j _keel_panic_overflow
.Lk9:
	mv s4, a0
	mv a1, s4
	call _kf_1
	mv s5, a0
	mv t0, s1
	li t1, 1
	sub a0, t0, t1
	xor t2, t0, t1
	xor t3, t0, a0
	and t2, t2, t3
	bgez t2, .Lk10
	j _keel_panic_overflow
.Lk10:
	mv s6, a0
	mv a1, s6
	call _kf_1
	mv s7, a0
	li a0, 2
	li a1, 3
	call _keel_alloc
	li t2, 1
	sb t2, -3(a0)
	mv t2, s5
	sd t2, 0(a0)
	mv t2, s7
	sd t2, 8(a0)
	mv s8, a0
	mv a0, s8
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_kf_2:			# many
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -16
	sd s1, 0(sp)
	sd s2, 8(sp)
L_kf_2_loop:
	mv s1, a1
	li a0, 2
	li a1, 0
	call _keel_alloc
	la t2, _kf_8
	sd t2, 0(a0)
	mv t2, s1
	sd t2, 8(a0)
	mv s2, a0
	mv a0, s2
	ld s1, 0(sp)
	ld s2, 8(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_kf_3:			# nested
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -272
	sd s1, 184(sp)
	sd s2, 192(sp)
	sd s3, 200(sp)
	sd s4, 208(sp)
	sd s5, 216(sp)
	sd s6, 224(sp)
	sd s7, 232(sp)
	sd s8, 240(sp)
	sd s9, 248(sp)
	sd s10, 256(sp)
	sd s11, 264(sp)
L_kf_3_loop:
	mv s2, a1
	call _keel_arena_open
	sd a0, 0(sp)
	li a0, 0
	sd a0, 8(sp)
	mv a1, s2
	call _kf_1
	mv s6, a0
	mv a0, s6
	mv s3, a0
	call _keel_arena_open
	sd a0, 16(sp)
	li a0, 0
	sd a0, 24(sp)
	mv t0, s2
	li t1, 1
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk11
	j _keel_panic_overflow
.Lk11:
	mv s7, a0
	mv a1, s7
	call _kf_1
	mv s4, a0
	mv a1, s4
	call _kf_0
	mv s8, a0
	mv a0, s4
	call _keel_drop
	li a0, 0
	li a1, 0
	call _keel_array_alloc
	mv s9, a0
	li a1, 1000
	mv a2, s9
	call _kf_7
	mv s10, a0
	mv a0, s10
	mv s5, a0
	mv t0, s5
	ld a0, 0(t0)
	mv s11, a0
	mv a0, s5
	call _keel_drop
	mv t0, s8
	mv t1, s11
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk12
	j _keel_panic_overflow
.Lk12:
	sd a0, 32(sp)
	call _keel_arena_close
	sd a0, 40(sp)
	ld a0, 32(sp)
	mv s1, a0
	mv t0, s1
	li t1, 0
	slt a0, t0, t1
	sd a0, 48(sp)
	ld t0, 48(sp)
	bnez t0, .Lk15
	j .Lk13
.Lk15:
	li a1, 45
	li a0, 1
	call _keel_perform
	sd a0, 64(sp)
	ld a0, 64(sp)
	sd a0, 72(sp)
	mv t0, s1
	li t1, 1
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk16
	j _keel_panic_overflow
.Lk16:
	sd a0, 80(sp)
	li t0, 0
	ld t1, 80(sp)
	sub a0, t0, t1
	xor t2, t0, t1
	xor t3, t0, a0
	and t2, t2, t3
	bgez t2, .Lk17
	j _keel_panic_overflow
.Lk17:
	sd a0, 88(sp)
	ld a0, 88(sp)
	sd a0, 96(sp)
	ld t0, 96(sp)
	li t1, 1
	add a0, t0, t1
	bgeu a0, t0, .Lk18
	j _keel_panic_overflow
.Lk18:
	sd a0, 104(sp)
	ld a1, 104(sp)
	call _kf_4
	sd a0, 112(sp)
	ld a0, 112(sp)
	sd a0, 56(sp)
	j .Lk14
.Lk13:
	mv a0, s1
	sd a0, 120(sp)
	ld a1, 120(sp)
	call _kf_4
	sd a0, 128(sp)
	ld a0, 128(sp)
	sd a0, 56(sp)
	j .Lk14
.Lk14:
	ld a0, 56(sp)
	sd a0, 136(sp)
	li a1, 10
	li a0, 1
	call _keel_perform
	sd a0, 144(sp)
	ld a0, 144(sp)
	sd a0, 152(sp)
	mv a1, s3
	call _kf_0
	sd a0, 160(sp)
	mv a0, s3
	call _keel_drop
	ld t0, 160(sp)
	mv t1, s1
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk19
	j _keel_panic_overflow
.Lk19:
	sd a0, 168(sp)
	call _keel_arena_close
	sd a0, 176(sp)
	ld a0, 168(sp)
	ld s1, 184(sp)
	ld s2, 192(sp)
	ld s3, 200(sp)
	ld s4, 208(sp)
	ld s5, 216(sp)
	ld s6, 224(sp)
	ld s7, 232(sp)
	ld s8, 240(sp)
	ld s9, 248(sp)
	ld s10, 256(sp)
	ld s11, 264(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_kf_4:			# printU64
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -112
	sd s1, 16(sp)
	sd s2, 24(sp)
	sd s3, 32(sp)
	sd s4, 40(sp)
	sd s5, 48(sp)
	sd s6, 56(sp)
	sd s7, 64(sp)
	sd s8, 72(sp)
	sd s9, 80(sp)
	sd s10, 88(sp)
	sd s11, 96(sp)
L_kf_4_loop:
	mv s1, a1
	mv t0, s1
	li t1, 10
	sltu a0, t0, t1
	mv s2, a0
	mv t0, s2
	bnez t0, .Lk22
	j .Lk20
.Lk22:
	mv t0, s1
	li t1, 48
	add a0, t0, t1
	bgeu a0, t0, .Lk23
	j _keel_panic_overflow
.Lk23:
	mv s4, a0
	mv a0, s4
	andi a0, a0, 255
	mv s5, a0
	mv a1, s5
	li a0, 1
	call _keel_perform
	mv s6, a0
	mv a0, s6
	ld s1, 16(sp)
	ld s2, 24(sp)
	ld s3, 32(sp)
	ld s4, 40(sp)
	ld s5, 48(sp)
	ld s6, 56(sp)
	ld s7, 64(sp)
	ld s8, 72(sp)
	ld s9, 80(sp)
	ld s10, 88(sp)
	ld s11, 96(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
.Lk20:
	mv t0, s1
	li t1, 10
	bnez t1, .Lk24
	j _keel_panic_div
.Lk24:
	divu a0, t0, t1
	mv s7, a0
	mv a1, s7
	call _kf_4
	mv s8, a0
	mv a0, s8
	sd a0, 0(sp)
	mv t0, s1
	li t1, 10
	bnez t1, .Lk25
	j _keel_panic_div
.Lk25:
	remu a0, t0, t1
	mv s9, a0
	mv t0, s9
	li t1, 48
	add a0, t0, t1
	bgeu a0, t0, .Lk26
	j _keel_panic_overflow
.Lk26:
	mv s10, a0
	mv a0, s10
	andi a0, a0, 255
	mv s11, a0
	mv a1, s11
	li a0, 1
	call _keel_perform
	sd a0, 8(sp)
	ld a0, 8(sp)
	ld s1, 16(sp)
	ld s2, 24(sp)
	ld s3, 32(sp)
	ld s4, 40(sp)
	ld s5, 48(sp)
	ld s6, 56(sp)
	ld s7, 64(sp)
	ld s8, 72(sp)
	ld s9, 80(sp)
	ld s10, 88(sp)
	ld s11, 96(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_kf_5:			# squares
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -16
	sd s1, 0(sp)
	sd s2, 8(sp)
L_kf_5_loop:
	mv s1, a1
	li a0, 2
	li a1, 0
	call _keel_alloc
	la t2, _kf_9
	sd t2, 0(a0)
	mv t2, s1
	sd t2, 8(a0)
	mv s2, a0
	mv a0, s2
	ld s1, 0(sp)
	ld s2, 8(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_kf_6:			# many/2
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -96
	sd s1, 8(sp)
	sd s2, 16(sp)
	sd s3, 24(sp)
	sd s4, 32(sp)
	sd s5, 40(sp)
	sd s6, 48(sp)
	sd s7, 56(sp)
	sd s8, 64(sp)
	sd s9, 72(sp)
	sd s10, 80(sp)
	sd s11, 88(sp)
L_kf_6_loop:
	mv s1, a1
	mv s2, a2
	mv t0, s1
	li t1, 0
	xor a0, t0, t1
	seqz a0, a0
	mv s4, a0
	mv t0, s4
	bnez t0, .Lk29
	j .Lk27
.Lk29:
	mv a0, s2
	ld s1, 8(sp)
	ld s2, 16(sp)
	ld s3, 24(sp)
	ld s4, 32(sp)
	ld s5, 40(sp)
	ld s6, 48(sp)
	ld s7, 56(sp)
	ld s8, 64(sp)
	ld s9, 72(sp)
	ld s10, 80(sp)
	ld s11, 88(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
.Lk27:
	mv t0, s1
	li t1, 1
	sub a0, t0, t1
	xor t2, t0, t1
	xor t3, t0, a0
	and t2, t2, t3
	bgez t2, .Lk30
	j _keel_panic_overflow
.Lk30:
	mv s6, a0
	call _keel_arena_open
	mv s10, a0
	li a0, 0
	mv s11, a0
	li a1, 6
	call _kf_1
	mv s3, a0
	mv a1, s3
	call _kf_0
	mv s7, a0
	mv a0, s3
	call _keel_drop
	call _keel_arena_close
	sd a0, 0(sp)
	mv t0, s2
	mv t1, s7
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk31
	j _keel_panic_overflow
.Lk31:
	mv s8, a0
	mv a1, s6
	mv a2, s8
	j L_kf_6_loop
	.p2align 2
_kf_7:			# squares/2
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -80
	sd s1, 0(sp)
	sd s2, 8(sp)
	sd s3, 16(sp)
	sd s4, 24(sp)
	sd s5, 32(sp)
	sd s6, 40(sp)
	sd s7, 48(sp)
	sd s8, 56(sp)
	sd s9, 64(sp)
L_kf_7_loop:
	mv s1, a1
	mv s2, a2
	mv t0, s1
	li t1, 0
	xor a0, t0, t1
	seqz a0, a0
	mv s3, a0
	mv t0, s3
	bnez t0, .Lk34
	j .Lk32
.Lk34:
	mv a0, s2
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	ld s9, 64(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
.Lk32:
	mv t0, s1
	li t1, 1
	sub a0, t0, t1
	xor t2, t0, t1
	xor t3, t0, a0
	and t2, t2, t3
	bgez t2, .Lk35
	j _keel_panic_overflow
.Lk35:
	mv s5, a0
	mv t0, s1
	mv t1, s1
	mul a0, t0, t1
	mulh t2, t0, t1
	srai t3, a0, 63
	beq t2, t3, .Lk36
	j _keel_panic_overflow
.Lk36:
	mv s6, a0
	mv a0, s6
	mv s7, a0
	mv a0, s2
	mv a1, s7
	call _keel_array_push
	mv s8, a0
	mv a1, s5
	mv a2, s8
	j L_kf_7_loop
	.p2align 2
_kf_8:			# λacc
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -96
	sd s1, 8(sp)
	sd s2, 16(sp)
	sd s3, 24(sp)
	sd s4, 32(sp)
	sd s5, 40(sp)
	sd s6, 48(sp)
	sd s7, 56(sp)
	sd s8, 64(sp)
	sd s9, 72(sp)
	sd s10, 80(sp)
	sd s11, 88(sp)
	ld t0, 8(a0)
	mv s2, t0
L_kf_8_loop:
	mv s1, a1
	call _keel_drop
	mv t0, s2
	li t1, 0
	xor a0, t0, t1
	seqz a0, a0
	mv s4, a0
	mv t0, s4
	bnez t0, .Lk39
	j .Lk37
.Lk39:
	mv a0, s1
	ld s1, 8(sp)
	ld s2, 16(sp)
	ld s3, 24(sp)
	ld s4, 32(sp)
	ld s5, 40(sp)
	ld s6, 48(sp)
	ld s7, 56(sp)
	ld s8, 64(sp)
	ld s9, 72(sp)
	ld s10, 80(sp)
	ld s11, 88(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
.Lk37:
	mv t0, s2
	li t1, 1
	sub a0, t0, t1
	xor t2, t0, t1
	xor t3, t0, a0
	and t2, t2, t3
	bgez t2, .Lk40
	j _keel_panic_overflow
.Lk40:
	mv s6, a0
	call _keel_arena_open
	mv s10, a0
	li a0, 0
	mv s11, a0
	li a1, 6
	call _kf_1
	mv s3, a0
	mv a1, s3
	call _kf_0
	mv s7, a0
	mv a0, s3
	call _keel_drop
	call _keel_arena_close
	sd a0, 0(sp)
	mv t0, s1
	mv t1, s7
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk41
	j _keel_panic_overflow
.Lk41:
	mv s8, a0
	mv a1, s6
	mv a2, s8
	ld s1, 8(sp)
	ld s2, 16(sp)
	ld s3, 24(sp)
	ld s4, 32(sp)
	ld s5, 40(sp)
	ld s6, 48(sp)
	ld s7, 56(sp)
	ld s8, 64(sp)
	ld s9, 72(sp)
	ld s10, 80(sp)
	ld s11, 88(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	tail _kf_6
	.p2align 2
_kf_9:			# λxs
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -80
	sd s1, 0(sp)
	sd s2, 8(sp)
	sd s3, 16(sp)
	sd s4, 24(sp)
	sd s5, 32(sp)
	sd s6, 40(sp)
	sd s7, 48(sp)
	sd s8, 56(sp)
	sd s9, 64(sp)
	ld t0, 8(a0)
	mv s1, t0
L_kf_9_loop:
	mv s2, a1
	call _keel_drop
	mv t0, s1
	li t1, 0
	xor a0, t0, t1
	seqz a0, a0
	mv s3, a0
	mv t0, s3
	bnez t0, .Lk44
	j .Lk42
.Lk44:
	mv a0, s2
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	ld s9, 64(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
.Lk42:
	mv t0, s1
	li t1, 1
	sub a0, t0, t1
	xor t2, t0, t1
	xor t3, t0, a0
	and t2, t2, t3
	bgez t2, .Lk45
	j _keel_panic_overflow
.Lk45:
	mv s5, a0
	mv t0, s1
	mv t1, s1
	mul a0, t0, t1
	mulh t2, t0, t1
	srai t3, a0, 63
	beq t2, t3, .Lk46
	j _keel_panic_overflow
.Lk46:
	mv s6, a0
	mv a0, s6
	mv s7, a0
	mv a0, s2
	mv a1, s7
	call _keel_array_push
	mv s8, a0
	mv a1, s5
	mv a2, s8
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	ld s9, 64(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	tail _kf_7
	.p2align 2
_kf_main:			# main
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -96
	sd s1, 0(sp)
	sd s2, 8(sp)
	sd s3, 16(sp)
	sd s4, 24(sp)
	sd s5, 32(sp)
	sd s6, 40(sp)
	sd s7, 48(sp)
	sd s8, 56(sp)
	sd s9, 64(sp)
	sd s10, 72(sp)
	sd s11, 80(sp)
L_kf_main_loop:
	li a1, 4
	call _kf_1
	mv s3, a0
	mv a0, s3
	mv s1, a0
	li a1, 5
	call _kf_1
	mv s2, a0
	mv a1, s2
	call _kf_0
	mv s4, a0
	mv a0, s2
	call _keel_drop
	mv a0, s4
	mv s5, a0
	li a1, 100
	li a2, 0
	call _kf_6
	mv s6, a0
	mv t0, s5
	mv t1, s6
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk47
	j _keel_panic_overflow
.Lk47:
	mv s7, a0
	li a1, 3
	call _kf_3
	mv s8, a0
	mv t0, s7
	mv t1, s8
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk48
	j _keel_panic_overflow
.Lk48:
	mv s9, a0
	mv a1, s1
	call _kf_0
	mv s10, a0
	mv a0, s1
	call _keel_drop
	mv t0, s9
	mv t1, s10
	add a0, t0, t1
	xor t2, t0, a0
	xor t3, t1, a0
	and t2, t2, t3
	bgez t2, .Lk49
	j _keel_panic_overflow
.Lk49:
	mv s11, a0
	mv a0, s11
	ld s1, 0(sp)
	ld s2, 8(sp)
	ld s3, 16(sp)
	ld s4, 24(sp)
	ld s5, 32(sp)
	ld s6, 40(sp)
	ld s7, 48(sp)
	ld s8, 56(sp)
	ld s9, 64(sp)
	ld s10, 72(sp)
	ld s11, 80(sp)
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_kp_0:			# print i64
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -16
	sd a0, 0(sp)
	call _keel_print_i64
	mv sp, s0
	ld ra, 8(sp)
	ld s0, 0(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_keel_alloc:
	li t4, 64
	bgtu a0, t4, .L_alloc_bump
	la t4, _keel_fl
	ld t4, 0(t4)
	slli t5, a0, 3
	add t4, t4, t5
	ld t5, 0(t4)
	beqz t5, .L_alloc_bump
	ld t6, 0(t5)
	sd t6, 0(t4)
	la t6, _keel_stats
	ld a6, 8(t6)
	addi a6, a6, 1
	sd a6, 8(t6)
	j .L_alloc_header
.L_alloc_bump:
	la t4, _keel_heap_ptr
	ld t5, 0(t4)
	slli t6, a0, 3
	add t6, t6, t5
	addi t6, t6, 8
	ld a6, 8(t4)
	bleu t6, a6, .Lk50
	j _keel_panic_oom
.Lk50:
	sd t6, 0(t4)
	addi t5, t5, 8
	la t6, _keel_stats
	ld a6, 0(t6)
	addi a6, a6, 1
	sd a6, 0(t6)
.L_alloc_header:
	slli t6, a0, 32
	slli a6, a1, 48
	or t6, t6, a6
	ori t6, t6, 1
	sd t6, -8(t5)
	mv a0, t5
	ret
	.p2align 2
_keel_arena_open:
	la t4, _keel_heap_ptr
	ld t5, 0(t4)
	addi t6, t5, 24
	ld a6, 8(t4)
	bleu t6, a6, .Lk51
	j _keel_panic_oom
.Lk51:
	sd t6, 0(t4)
	la t4, _keel_arena_base
	ld t6, 0(t4)
	sd t6, 0(t5)
	la a6, _keel_arena_top
	ld a1, 0(a6)
	sd a1, 8(t5)
	sd t5, 0(a6)
	la a1, _keel_stats
	ld a1, 0(a1)
	sd a1, 16(t5)
	bgeu t6, t5, .Lk52
	j .L_arena_keep
.Lk52:
	sd t5, 0(t4)
.L_arena_keep:
	la t4, _keel_nofree
	la t5, _keel_fl
	sd t4, 0(t5)
	li a0, 0
	ret
	.p2align 2
_keel_arena_close:
	la a6, _keel_arena_top
	ld t5, 0(a6)
	ld t6, 8(t5)
	sd t6, 0(a6)
	ld t6, 0(t5)
	la t4, _keel_arena_base
	sd t6, 0(t4)
	addi t6, t6, 1
	beqz t6, .Lk53
	j .L_close_inner
.Lk53:
	la t4, _keel_freelists
	la t6, _keel_fl
	sd t4, 0(t6)
.L_close_inner:
	la t4, _keel_stats
	ld t6, 0(t4)
	ld a1, 16(t5)
	sub t6, t6, a1
	ld a1, 24(t4)
	add a1, a1, t6
	sd a1, 24(t4)
	ld a1, 8(t5)
	bnez a1, .Lk54
	j .L_close_outermost
.Lk54:
	ld a6, 16(a1)
	add a6, a6, t6
	sd a6, 16(a1)
.L_close_outermost:
	la t4, _keel_heap_ptr
	sd t5, 0(t4)
	li a0, 0
	ret
	.p2align 2
_keel_drop:
	addi sp, sp, -32
	sd ra, 24(sp)
.L_drop_top:
	lw t0, -8(a0)
	bltz t0, .L_drop_ret
	bnez t0, .Lk55
	j _keel_panic_rc
.Lk55:
	addiw t0, t0, -1
	sw t0, -8(a0)
	bnez t0, .L_drop_ret
	la t3, _keel_arena_base
	ld t3, 0(t3)
	bltu a0, t3, .Lk56
	j .L_drop_ret
.Lk56:
	la t6, _keel_stats
	ld a6, 24(t6)
	addi a6, a6, 1
	sd a6, 24(t6)
	sd a0, 0(sp)
	ld t2, -8(a0)
	srli t2, t2, 48
	lbu t3, -3(a0)
	addi t3, t3, -255
	beqz t3, .L_drop_array
.L_drop_loop:
	beqz t2, .L_drop_free
	addi t3, t2, -1
	and t3, t2, t3
	beqz t3, .L_drop_last
	neg t3, t2
	and t3, t2, t3
	xor t2, t2, t3
	sd t2, 8(sp)
	li t4, 0
.Lk57:
	li t5, 1
	beq t3, t5, .Lk58
	srli t3, t3, 1
	addi t4, t4, 8
	j .Lk57
.Lk58:
	ld t0, 0(sp)
	add t0, t0, t4
	ld a0, 0(t0)
	call _keel_drop
	ld t2, 8(sp)
	j .L_drop_loop
.L_drop_last:
	mv t3, t2
	li t4, 0
.Lk59:
	li t5, 1
	beq t3, t5, .Lk60
	srli t3, t3, 1
	addi t4, t4, 8
	j .Lk59
.Lk60:
	ld a0, 0(sp)
	add t0, a0, t4
	ld t0, 0(t0)
	sd t0, 8(sp)
	call _keel_free_block
	ld a0, 8(sp)
	j .L_drop_top
.L_drop_free:
	ld a0, 0(sp)
	call _keel_free_block
.L_drop_ret:
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
.L_drop_array:
	andi t3, t2, 2
	beqz t3, .L_drop_free
	ld t2, 0(a0)
.L_drop_elems:
	beqz t2, .L_drop_free
	addi t2, t2, -1
	sd t2, 8(sp)
	ld t0, 0(sp)
	slli t3, t2, 3
	add t0, t0, t3
	ld a0, 16(t0)
	call _keel_drop
	ld t2, 8(sp)
	j .L_drop_elems
	.p2align 2
_keel_free_block:
	ld t0, -8(a0)
	srli t0, t0, 32
	andi t0, t0, 0xFF
	li t1, 64
	bgtu t0, t1, .L_free_ret
	la t1, _keel_freelists
	slli t0, t0, 3
	add t1, t1, t0
	ld t2, 0(t1)
	sd t2, 0(a0)
	sd a0, 0(t1)
.L_free_ret:
	ret
	.p2align 2
_keel_array_alloc:
	addi sp, sp, -32
	sd ra, 24(sp)
	sd a0, 0(sp)
	sd a1, 8(sp)
	addi a0, a0, 2
	li a1, 0
	call _keel_alloc
	ld t0, 0(sp)
	ld t1, 8(sp)
	addi t2, t0, 2
	li t3, 0xFF
	bltu t2, t3, .L_aalloc_size
	mv t2, t3
.L_aalloc_size:
	slli t2, t2, 32
	ori t2, t2, 1
	li t3, 0xFF
	slli t3, t3, 40
	or t2, t2, t3
	slli t1, t1, 49
	or t2, t2, t1
	sd t2, -8(a0)
	sd zero, 0(a0)
	sd t0, 8(a0)
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
	.p2align 2
_keel_array_new:
	addi sp, sp, -48
	sd ra, 40(sp)
	bgez a0, .Lk61
	j _keel_panic_bounds
.Lk61:
	sd a1, 0(sp)
	sd a2, 8(sp)
	sd a0, 16(sp)
	mv a1, a2
	call _keel_array_alloc
	ld t0, 16(sp)
	ld t1, 0(sp)
	ld t2, 8(sp)
	sd t0, 0(a0)
	li t3, 0
.L_anew_fill:
	bgeu t3, t0, .L_anew_filled
	slli t4, t3, 3
	add t4, t4, a0
	sd t1, 16(t4)
	addi t3, t3, 1
	j .L_anew_fill
.L_anew_filled:
	beqz t2, .L_anew_ret
	beqz t0, .L_anew_drop
	lw t4, -8(t1)
	bltz t4, .L_anew_ret
	addw t4, t4, t0
	addiw t4, t4, -1
	sw t4, -8(t1)
	j .L_anew_ret
.L_anew_drop:
	sd a0, 16(sp)
	mv a0, t1
	call _keel_drop
	ld a0, 16(sp)
.L_anew_ret:
	ld ra, 40(sp)
	addi sp, sp, 48
	ret
	.p2align 2
_keel_array_clone:
	addi sp, sp, -48
	sd ra, 40(sp)
	sd a0, 0(sp)
	ld t0, -8(a0)
	srli t0, t0, 49
	andi t0, t0, 1
	mv a0, a1
	mv a1, t0
	call _keel_array_alloc
	ld t0, 0(sp)
	ld t1, 0(t0)
	sd t1, 0(a0)
	li t2, 0
.L_aclone_copy:
	bgeu t2, t1, .L_aclone_copied
	slli t3, t2, 3
	add t4, t0, t3
	ld t5, 16(t4)
	add t4, a0, t3
	sd t5, 16(t4)
	addi t2, t2, 1
	j .L_aclone_copy
.L_aclone_copied:
	lw t2, -8(t0)
	li t3, 1
	bne t2, t3, .L_aclone_shared
	sw zero, -8(t0)
	la t1, _keel_arena_base
	ld t1, 0(t1)
	bltu t0, t1, .Lk62
	j .L_aclone_ret
.Lk62:
	la t6, _keel_stats
	ld a6, 24(t6)
	addi a6, a6, 1
	sd a6, 24(t6)
	sd a0, 8(sp)
	mv a0, t0
	call _keel_free_block
	ld a0, 8(sp)
	j .L_aclone_ret
.L_aclone_shared:
	ld t3, -8(t0)
	srli t3, t3, 49
	andi t3, t3, 1
	beqz t3, .L_aclone_dec
	li t3, 0
.L_aclone_dup:
	bgeu t3, t1, .L_aclone_dec
	slli t4, t3, 3
	add t4, t4, t0
	ld t4, 16(t4)
	lw t5, -8(t4)
	bltz t5, .L_aclone_next
	addiw t5, t5, 1
	sw t5, -8(t4)
.L_aclone_next:
	addi t3, t3, 1
	j .L_aclone_dup
.L_aclone_dec:
	addiw t2, t2, -1
	sw t2, -8(t0)
.L_aclone_ret:
	ld ra, 40(sp)
	addi sp, sp, 48
	ret
	.p2align 2
_keel_array_set:
	addi sp, sp, -32
	sd ra, 24(sp)
	ld t0, 0(a0)
	bltu a1, t0, .Lk63
	j _keel_panic_bounds
.Lk63:
	lw t1, -8(a0)
	li t2, 1
	beq t1, t2, .L_aset_store
	sd a1, 0(sp)
	sd a2, 8(sp)
	ld a1, 8(a0)
	call _keel_array_clone
	ld a1, 0(sp)
	ld a2, 8(sp)
.L_aset_store:
	slli t0, a1, 3
	add t0, t0, a0
	ld t1, 16(t0)
	sd a2, 16(t0)
	ld t2, -8(a0)
	srli t2, t2, 49
	andi t2, t2, 1
	beqz t2, .L_aset_ret
	sd a0, 0(sp)
	mv a0, t1
	call _keel_drop
	ld a0, 0(sp)
.L_aset_ret:
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
	.p2align 2
_keel_array_push:
	addi sp, sp, -32
	sd ra, 24(sp)
	sd a1, 0(sp)
	ld t0, 0(a0)
	ld t1, 8(a0)
	bgeu t0, t1, .L_apush_grow
	lw t2, -8(a0)
	li t3, 1
	beq t2, t3, .L_apush_store
	mv a1, t1
	call _keel_array_clone
	j .L_apush_store
.L_apush_grow:
	slli a1, t1, 1
	li t3, 4
	bgeu a1, t3, .L_apush_cap
	mv a1, t3
.L_apush_cap:
	call _keel_array_clone
.L_apush_store:
	ld t0, 0(a0)
	slli t1, t0, 3
	add t1, t1, a0
	ld a1, 0(sp)
	sd a1, 16(t1)
	addi t0, t0, 1
	sd t0, 0(a0)
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
	.p2align 2
_keel_array_pop:
	addi sp, sp, -32
	sd ra, 24(sp)
	ld t0, 0(a0)
	bnez t0, .Lk64
	j _keel_panic_bounds
.Lk64:
	lw t1, -8(a0)
	li t2, 1
	beq t1, t2, .L_apop_take
	ld a1, 8(a0)
	call _keel_array_clone
.L_apop_take:
	ld t0, 0(a0)
	addi t0, t0, -1
	sd t0, 0(a0)
	ld t2, -8(a0)
	srli t2, t2, 49
	andi t2, t2, 1
	beqz t2, .L_apop_ret
	slli t1, t0, 3
	add t1, t1, a0
	sd a0, 0(sp)
	ld a0, 16(t1)
	call _keel_drop
	ld a0, 0(sp)
.L_apop_ret:
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
	.p2align 2
_keel_drop_reuse:
	addi sp, sp, -32
	sd ra, 24(sp)
	lw t0, -8(a0)
	bltz t0, .L_reuse_none
	bnez t0, .Lk65
	j _keel_panic_rc
.Lk65:
	li t1, 1
	bne t0, t1, .L_reuse_shared
	la t6, _keel_stats
	ld a6, 24(t6)
	addi a6, a6, 1
	sd a6, 24(t6)
	sd a0, 0(sp)
	ld t2, -8(a0)
	srli t2, t2, 48
.L_reuse_loop:
	beqz t2, .L_reuse_done
	neg t3, t2
	and t3, t2, t3
	xor t2, t2, t3
	sd t2, 8(sp)
	li t4, 0
.Lk66:
	li t5, 1
	beq t3, t5, .Lk67
	srli t3, t3, 1
	addi t4, t4, 8
	j .Lk66
.Lk67:
	ld t0, 0(sp)
	add t0, t0, t4
	ld a0, 0(t0)
	call _keel_drop
	ld t2, 8(sp)
	j .L_reuse_loop
.L_reuse_done:
	ld a0, 0(sp)
	sw zero, -8(a0)
	j .L_reuse_ret
.L_reuse_shared:
	addiw t0, t0, -1
	sw t0, -8(a0)
.L_reuse_none:
	li a0, 0
.L_reuse_ret:
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
	.p2align 2
_keel_perform:
	addi sp, sp, -32
	sd ra, 24(sp)
	la t0, _keel_handlers
	ld t1, 0(t0)
	sd t1, 0(sp)
.L_perform_frame:
	beqz t1, .L_perform_machine
	ld t2, 8(t1)
	addi t3, t1, 16
.L_perform_scan:
	beqz t2, .L_perform_next
	ld t4, 0(t3)
	beq t4, a0, .L_perform_found
	addi t3, t3, 16
	addi t2, t2, -1
	j .L_perform_scan
.L_perform_next:
	ld t1, 0(t1)
	j .L_perform_frame
.L_perform_found:
	ld t4, 0(t1)
	sd t4, 0(t0)
	ld a0, 8(t3)
	lw t5, -8(a0)
	bltz t5, .L_perform_call
	addiw t5, t5, 1
	sw t5, -8(a0)
.L_perform_call:
	ld t6, 0(a0)
	jalr t6
	ld t1, 0(sp)
	la t0, _keel_handlers
	sd t1, 0(t0)
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
.L_perform_machine:
	li t0, 1
	beq a0, t0, .L_putc_op
	li t0, 2
	beq a0, t0, .L_getc_op
	li t0, 3
	beq a0, t0, .L_read8
	li t0, 4
	beq a0, t0, .L_read32
	li t0, 5
	beq a0, t0, .L_write8
	li t0, 6
	beq a0, t0, .L_write32
	li t0, 7
	beq a0, t0, .L_open_op
	li t0, 8
	beq a0, t0, .L_no_file
	li t0, 9
	beq a0, t0, .L_no_file
	bnez a0, .L_perform_unhandled
	mv a0, a1
	call _keel_print_i64
	li a0, 10
	call _keel_putc
	li a0, 0
	j .L_machine_ret
.L_putc_op:
	mv a0, a1
	call _keel_putc
	li a0, 0
	j .L_machine_ret
.L_getc_op:
	li t0, 0x10000000
	lbu t1, 5(t0)
	andi t1, t1, 1
	li a0, -1
	beqz t1, .L_machine_ret
	lbu a0, 0(t0)
	j .L_machine_ret
.L_open_op:
	mv a0, a1
	call _keel_drop
.L_no_file:
	li a0, -1
	j .L_machine_ret
.L_read8:
	lbu a0, 0(a1)
	j .L_machine_ret
.L_read32:
	lwu a0, 0(a1)
	j .L_machine_ret
.L_write8:
	ld t0, 0(a1)
	ld t1, 8(a1)
	sb t1, 0(t0)
	j .L_write_done
.L_write32:
	ld t0, 0(a1)
	ld t1, 8(a1)
	sw t1, 0(t0)
.L_write_done:
	mv a0, a1
	call _keel_drop
	li a0, 0
.L_machine_ret:
	ld ra, 24(sp)
	addi sp, sp, 32
	ret
.L_perform_unhandled:
	j _keel_panic_unhandled
	.p2align 2
_keel_putc:
	li t0, 0x10000000
.L_putc_wait:
	lbu t1, 5(t0)
	andi t1, t1, 0x20
	beqz t1, .L_putc_wait
	sb a0, 0(t0)
	ret
	.p2align 2
_keel_print_str:
	addi sp, sp, -16
	sd ra, 8(sp)
	mv a2, a0
.L_str_loop:
	lbu a0, 0(a2)
	beqz a0, .L_str_done
	call _keel_putc
	addi a2, a2, 1
	j .L_str_loop
.L_str_done:
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.p2align 2
_keel_print_u64:
	addi sp, sp, -48
	sd ra, 40(sp)
	addi a2, sp, 32
	sb zero, 0(a2)
	li a3, 10
.L_u64_loop:
	remu a4, a0, a3
	divu a0, a0, a3
	addi a4, a4, 48
	addi a2, a2, -1
	sb a4, 0(a2)
	bnez a0, .L_u64_loop
	mv a0, a2
	call _keel_print_str
	ld ra, 40(sp)
	addi sp, sp, 48
	ret
	.p2align 2
_keel_print_i64:
	bgez a0, .L_i64_pos
	addi sp, sp, -16
	sd ra, 8(sp)
	sd a0, 0(sp)
	li a0, 45
	call _keel_putc
	ld a0, 0(sp)
	neg a0, a0
	ld ra, 8(sp)
	addi sp, sp, 16
.L_i64_pos:
	tail _keel_print_u64
	.p2align 2
_keel_exit:
	li t0, 0x100000
	li t1, 0x5555
	beqz a0, .L_exit_write
	slli t1, a0, 16
	li t2, 0x3333
	or t1, t1, t2
.L_exit_write:
	sw t1, 0(t0)
.L_exit_hang:
	j .L_exit_hang
	.p2align 2
_keel_panic_unhandled:
	la a0, _keel_s8
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_div:
	la a0, _keel_s9
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_bounds:
	la a0, _keel_s10
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_overflow:
	la a0, _keel_s11
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_oom:
	la a0, _keel_s12
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_rc:
	la a0, _keel_s13
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.data
	.p2align 3
	.dword 0x80000000		# header: immortal
_kc_0:			# static block of check
	.dword _kf_0
	.dword 0x80000000		# header: immortal
_kc_1:			# static block of make@arena
	.dword _kf_1
	.dword 0x80000000		# header: immortal
_kc_2:			# static block of many
	.dword _kf_2
	.dword 0x80000000		# header: immortal
_kc_3:			# static block of nested
	.dword _kf_3
	.dword 0x80000000		# header: immortal
_kc_4:			# static block of printU64
	.dword _kf_4
	.dword 0x80000000		# header: immortal
_kc_5:			# static block of squares
	.dword _kf_5
	.dword 2147483648		# header: immortal, tag 0
_kn_0:			# every constructor without fields with this tag
	.dword 0
_keel_heap_ptr:
	.dword _keel_heap
	.dword _keel_heap+67108864
_keel_arena_base:
	.dword -1
_keel_arena_top:
	.dword 0
_keel_fl:
	.dword _keel_freelists
_keel_freelists:
	.zero 520
_keel_nofree:
	.zero 520
_keel_stats:
	.zero 32
_keel_handlers:
	.zero 8
	.bss
	.p2align 4
_keel_heap:
	.zero 67108864
_keel_stack:
	.zero 8388608
_keel_stack_top:
	.section .rodata
_keel_s1:	.asciz "\n"
_keel_s3:	.asciz " allocs="
_keel_s6:	.asciz " freed="
_keel_s5:	.asciz " inplace="
_keel_s7:	.asciz " live="
_keel_s4:	.asciz " recycled="
_keel_s2:	.asciz "keel-stats:"
_keel_s11:	.asciz "panic: arithmetic overflow\n"
_keel_s10:	.asciz "panic: array index out of bounds\n"
_keel_s9:	.asciz "panic: division by zero\n"
_keel_s12:	.asciz "panic: out of memory\n"
_keel_s13:	.asciz "panic: reference count error\n"
_keel_s8:	.asciz "panic: unhandled operation\n"
_keel_s0:	.asciz "result: "
