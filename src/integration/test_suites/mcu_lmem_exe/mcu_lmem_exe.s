#define STDOUT 0xd0580000

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

    # Jump to main in RAM
    la a0, 0x80010000    # Load the address of the main program in RAM into a0
    jalr ra, 0(a0)       # Jump to the address in a0 and link return address to ra

_finish:
    li x3, STDOUT
    sb a0, 0(x3)             // Write the return value (a0) to STDOUT
    beq x0, x0, _finish      // Infinite loop

.align 4
_trap:
    li a0, 1                 // Set a0 to failure
    j _finish                // Jump to finish

.section .data
.global main
main:
    // Instructions to execute
    li x3, STDOUT            // Load STDOUT address
    la x4, hw_data           // Load address of hw_data

loop:
    lb x5, 0(x4)             // Load a byte from hw_data
    sb x5, 0(x3)             // Store byte to STDOUT
    addi x4, x4, 1           // Move to the next byte
    bnez x5, loop            // Continue until null byte is encountered

    li a0, 0xff              // Set a0 to success value (after loop)

_end:
    li x3, STDOUT
    sb a0, 0(x3)             // Write the return value (a0) to STDOUT
    beq x0, x0, _end      // Infinite loop

.section .dccm
.global hw_data
hw_data:
    .ascii "-------------------------\n"
    .ascii "Hello World from MCU\n"
    .ascii "-------------------------\n"
    .byte 0                  // Null-terminated string

