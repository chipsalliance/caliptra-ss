#define STDOUT 0xd0580000

// Code to execute
.section .text
.global _start
_start:

    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    // Set trap handler
    la x1, _trap
    csrw mtvec, x1

    // Enable Caches in MRAC
    li x1, 0x5f555555
    csrw 0x7c0, x1

    // Load string from hw_data
    // and write to stdout address

    li x3, STDOUT
    la x4, hw_data

loop:
   lb x5, 0(x4)
   sb x5, 0(x3)
   addi x4, x4, 1
   bnez x5, loop
   li a0, 0xff # success

// Write return value (a0) from printf to STDOUT for TB to terminate test.
_finish:
    li x3, STDOUT
    sb a0, 0(x3)
    beq x0, x0, _finish
.rept 100
    nop
.endr

.align 4
_trap:
    li a0, 1 # failure
    j _finish

.section .dccm
.global hw_data
hw_data:
.ascii "-------------------------\n"
.ascii "Hello World from MCU\n"
.ascii "-------------------------\n"
.byte 0
