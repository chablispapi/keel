	.section .text.start, "ax"
	.globl _start
	.p2align 2
_start:
	la sp, _keel_stack_top
	la t0, _keel_trap
	csrw mtvec, t0
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
_kf_main:			# main
	addi sp, sp, -16
	sd ra, 8(sp)
	sd s0, 0(sp)
	mv s0, sp
	addi sp, sp, -16
	sd s1, 0(sp)
L_kf_main_loop:
	li a0, 2
	li a1, 8589934592
	call _keel_alloc
	li t2, 33570816
	sd t2, 0(a0)
	li t2, 0
	sd t2, 8(a0)
	mv s1, a0
	mv a1, s1
	li a0, 6
	call _keel_perform
	mv s1, a0
	mv a0, s1
	mv s1, a0
	li t0, 33570816
	li t1, 4
	add a0, t0, t1
	mv s1, a0
	li a0, 2
	li a1, 8589934592
	call _keel_alloc
	mv t2, s1
	sd t2, 0(a0)
	li t2, 0
	sd t2, 8(a0)
	mv s1, a0
	mv a1, s1
	li a0, 6
	call _keel_perform
	mv s1, a0
	mv a0, s1
	mv s1, a0
	li a0, 2
	li a1, 8589934592
	call _keel_alloc
	li t2, 772
	sd t2, 0(a0)
	li t2, 128
	sd t2, 8(a0)
	mv s1, a0
	mv a1, s1
	li a0, 8
	call _keel_perform
	mv s1, a0
	mv a0, s1
	mv s1, a0
	li a0, 2
	li a1, 8589934592
	call _keel_alloc
	li t2, 768
	sd t2, 0(a0)
	li t2, 8
	sd t2, 8(a0)
	mv s1, a0
	mv a1, s1
	li a0, 8
	call _keel_perform
	mv s1, a0
	mv a0, s1
	mv s1, a0
	li a0, 0
	ld s1, 0(sp)
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
	beqz a0, .L_alloc_link0
	ld t6, 0(t5)
.L_alloc_pop:
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
	bleu t6, a6, .Lk0
	j _keel_panic_oom
.Lk0:
	sd t6, 0(t4)
	addi t5, t5, 8
	la t6, _keel_stats
	ld a6, 0(t6)
	addi a6, a6, 1
	sd a6, 0(t6)
.L_alloc_header:
	ori t6, a1, 1024
	sd t6, -8(t5)
	mv a0, t5
	ret
.L_alloc_link0:
	lw t6, -4(t5)
	beqz t6, .L_alloc_pop
	slli t6, t6, 3
	add t6, t6, t5
	j .L_alloc_pop
	.p2align 2
_keel_drop:
	addi sp, sp, -32
	sd ra, 24(sp)
.L_drop_top:
	lw t0, -8(a0)
	bltz t0, .L_drop_ret
	addiw t0, t0, -1024
	bgez t0, .Lk5
	j _keel_panic_rc
.Lk5:
	sw t0, -8(a0)
	srliw t1, t0, 10
	bnez t1, .L_drop_ret
	la t3, _keel_arena_base
	ld t3, 0(t3)
	bltu a0, t3, .Lk6
	j .L_drop_ret
.Lk6:
	la t6, _keel_stats
	ld a6, 24(t6)
	addi a6, a6, 1
	sd a6, 24(t6)
	sd a0, 0(sp)
	andi t3, t0, 0x3ff
	li t1, 509
	bgeu t3, t1, .L_drop_special
	ld t2, -8(a0)
	slli t2, t2, 7
	srli t2, t2, 47
	srli t5, t2, 16
	sd t5, 16(sp)
	slli t2, t2, 48
	srli t2, t2, 48
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
.Lk7:
	li t5, 1
	beq t3, t5, .Lk8
	srli t3, t3, 1
	addi t4, t4, 8
	j .Lk7
.Lk8:
	ld t0, 0(sp)
	ld t5, 16(sp)
	bnez t5, .Lk9
	add t6, t0, t4
	ld a0, 0(t6)
	j .Lk10
.Lk9:
	srli t6, t4, 1
	add t6, t0, t6
	lw a0, 0(t6)
	slli a0, a0, 3
	add a0, t0, a0
.Lk10:
	call _keel_drop
	ld t2, 8(sp)
	j .L_drop_loop
.L_drop_last:
	mv t3, t2
	li t4, 0
.Lk11:
	li t5, 1
	beq t3, t5, .Lk12
	srli t3, t3, 1
	addi t4, t4, 8
	j .Lk11
.Lk12:
	ld a0, 0(sp)
	ld t5, 16(sp)
	bnez t5, .Lk13
	add t6, a0, t4
	ld t0, 0(t6)
	j .Lk14
.Lk13:
	srli t6, t4, 1
	add t6, a0, t6
	lw t0, 0(t6)
	slli t0, t0, 3
	add t0, a0, t0
.Lk14:
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
.L_drop_special:
	li t4, 512
	bltu t3, t4, .L_drop_array
	la t4, _keel_layouts
	addi t2, t3, -512
	slli t2, t2, 2
	add t4, t4, t2
	lwu t2, 0(t4)
	srli t2, t2, 8
	srli t5, t2, 16
	sd t5, 16(sp)
	slli t2, t2, 48
	srli t2, t2, 48
	j .L_drop_loop
.L_drop_array:
	li t1, 511
	beq t3, t1, .L_drop_elems_ptr
	j .L_drop_free
.L_drop_elems_ptr:
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
	lbu t0, -4(a0)
	lw t1, -8(a0)
	andi t1, t1, 0x200
	beqz t1, .L_free_size
	lw t0, -8(a0)
	andi t0, t0, 0x1ff
	la t1, _keel_layouts
	slli t0, t0, 2
	add t1, t1, t0
	lbu t0, 0(t1)
.L_free_size:
	li t1, 64
	bgtu t0, t1, .L_free_ret
	la t1, _keel_freelists
	slli t0, t0, 3
	add t1, t1, t0
	ld t2, 0(t1)
	beqz t0, .L_free_link0
	sd t2, 0(a0)
	sd a0, 0(t1)
	ret
.L_free_link0:
	beqz t2, .L_free_link
	sub t2, t2, a0
	srai t2, t2, 3
.L_free_link:
	sw t2, -4(a0)
	sd a0, 0(t1)
.L_free_ret:
	ret
	.p2align 2
_keel_array_alloc:
	addi sp, sp, -32
	sd ra, 24(sp)
	sd a0, 0(sp)
	sd a1, 8(sp)
	snez t0, a1
	addi t0, t0, 2
	sll a0, a0, t0
	addi a0, a0, 23
	srli a0, a0, 3
	sd a0, 16(sp)
	li a1, 0
	call _keel_alloc
	ld t0, 0(sp)
	ld t1, 8(sp)
	li t2, 1533
	add t2, t2, t1
	ld t3, 16(sp)
	li t4, 0xFF
	bltu t3, t4, .L_aalloc_size
	mv t3, t4
.L_aalloc_size:
	slli t3, t3, 32
	or t2, t2, t3
	sd t2, -8(a0)
	sd zero, 0(a0)
	sd t0, 8(a0)
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
	addiw t5, t5, 1024
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
	beq a0, t0, .L_csr_read
	li t0, 8
	beq a0, t0, .L_csr_set
	li t0, 9
	beq a0, t0, .L_wfi
	li t0, 10
	beq a0, t0, .L_open_op
	li t0, 13
	beq a0, t0, .L_open_op
	li t0, 14
	beq a0, t0, .L_open_op
	li t0, 15
	beq a0, t0, .L_net_drop
	li t0, 11
	beq a0, t0, .L_no_file
	li t0, 12
	beq a0, t0, .L_no_file
	li t0, 16
	bgeu a0, t0, .L_no_net
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
.L_no_net:
	li t0, 23
	beq a0, t0, .L_net_nowait
	li t0, 16
	beq a0, t0, .L_net_drop
	li t0, 19
	beq a0, t0, .L_net_drop
	li t0, 20
	beq a0, t0, .L_net_drop
	li t0, 21
	beq a0, t0, .L_net_recv
	li t0, 22
	beq a0, t0, .L_net_zero
	li t0, 24
	beq a0, t0, .L_net_zero
	j .L_no_file
.L_net_drop:
	mv a0, a1
	call _keel_drop
	j .L_no_file
.L_net_nowait:
	mv a0, a1
	call _keel_drop
	li a0, -2
	j .L_machine_ret
.L_net_recv:
	li a0, 0
	li a1, 0
	call _keel_array_alloc
	j .L_machine_ret
.L_net_zero:
	li a0, 0
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
.L_csr_read:
	li t0, 768
	beq a1, t0, .L_csrr_mstatus
	li t0, 772
	beq a1, t0, .L_csrr_mie
	li t0, 834
	beq a1, t0, .L_csrr_mcause
	li t0, 836
	beq a1, t0, .L_csrr_mip
	j _keel_panic_csr
.L_csrr_mstatus:
	csrr a0, mstatus
	j .L_machine_ret
.L_csrr_mie:
	csrr a0, mie
	j .L_machine_ret
.L_csrr_mcause:
	csrr a0, mcause
	j .L_machine_ret
.L_csrr_mip:
	csrr a0, mip
	j .L_machine_ret
.L_csr_set:
	ld t0, 0(a1)
	ld t1, 8(a1)
	li t2, 768
	beq t0, t2, .L_csrs_mstatus
	li t2, 772
	beq t0, t2, .L_csrs_mie
	li t2, 834
	beq t0, t2, .L_csrs_mcause
	li t2, 836
	beq t0, t2, .L_csrs_mip
	j _keel_panic_csr
.L_csrs_mstatus:
	csrs mstatus, t1
	j .L_write_done
.L_csrs_mie:
	csrs mie, t1
	j .L_write_done
.L_csrs_mcause:
	csrs mcause, t1
	j .L_write_done
.L_csrs_mip:
	csrs mip, t1
	j .L_write_done
.L_wfi:
	wfi
	li a0, 0
	j .L_machine_ret
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
_keel_trap:
	la sp, _keel_stack_top
	la a0, _keel_s8
	call _keel_print_str
	csrr a0, mcause
	call _keel_print_hex
	la a0, _keel_s9
	call _keel_print_str
	csrr a0, mepc
	call _keel_print_hex
	la a0, _keel_s10
	call _keel_print_str
	csrr a0, mtval
	call _keel_print_hex
	la a0, _keel_s1
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_print_hex:
	addi sp, sp, -48
	sd ra, 40(sp)
	addi a2, sp, 32
	sb zero, 0(a2)
	li a3, 10
.L_hex_loop:
	andi a4, a0, 15
	srli a0, a0, 4
	blt a4, a3, .L_hex_digit
	addi a4, a4, 39
.L_hex_digit:
	addi a4, a4, 48
	addi a2, a2, -1
	sb a4, 0(a2)
	bnez a0, .L_hex_loop
	addi a2, a2, -2
	li a4, 48
	sb a4, 0(a2)
	li a4, 120
	sb a4, 1(a2)
	mv a0, a2
	call _keel_print_str
	ld ra, 40(sp)
	addi sp, sp, 48
	ret
	.p2align 2
_keel_panic_unhandled:
	la a0, _keel_s11
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_csr:
	la a0, _keel_s12
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_oom:
	la a0, _keel_s16
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.p2align 2
_keel_panic_rc:
	la a0, _keel_s17
	call _keel_print_str
	li a0, 101
	tail _keel_exit
	.data
	.p2align 3
	.p2align 2
_keel_layouts:
	.p2align 3
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
_keel_hi:
	.zero 32
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
_keel_s9:	.asciz " mepc="
_keel_s10:	.asciz " mtval="
_keel_s4:	.asciz " recycled="
_keel_s2:	.asciz "keel-stats:"
_keel_s15:	.asciz "panic: arithmetic overflow\n"
_keel_s14:	.asciz "panic: array index out of bounds\n"
_keel_s12:	.asciz "panic: csrRead or csrSet of a CSR other than mstatus, mie, mcause, mip\n"
_keel_s13:	.asciz "panic: division by zero\n"
_keel_s16:	.asciz "panic: out of memory\n"
_keel_s17:	.asciz "panic: reference count error\n"
_keel_s8:	.asciz "panic: trap mcause="
_keel_s11:	.asciz "panic: unhandled operation\n"
_keel_s0:	.asciz "result: "
