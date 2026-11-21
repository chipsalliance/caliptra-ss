# SPDX-License-Identifier: Apache-2.0
#define PMP_PATCH_ASM
#include "mcu_pmp_rom_patch.h"

.option push
.option rvc
.option norelax

.section .mcu_sram.support, "ax", @progbits
# Direct mtvec requires four-byte BASE alignment, unrelated to ROM interception.
.balign 4
.global sram_patch_begin
.global sram_trap_entry
.type sram_trap_entry, @function
# Save only registers used by support; a5 is dead until the displaced SRLI writes it.
sram_patch_begin:
sram_trap_entry:
    addi sp, sp, -PATCH_CONTEXT_BYTES
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    la t0, patch_state
    csrr t1, mcause
    sw t1, PS_CAUSE(t0)
    csrr t1, mepc
    sw t1, PS_MEPC(t0)
    lw t1, PS_TRAPS(t0)
    addi t1, t1, 1
    sw t1, PS_TRAPS(t0)
    lw t1, PS_TOTAL_TRAPS(t0)
    addi t1, t1, 1
    sw t1, PS_TOTAL_TRAPS(t0)

    li t2, REJECT_CAUSE
    lw t1, PS_CAUSE(t0)
    li a5, 1
    bne t1, a5, .Lreject
    li t2, REJECT_PC
    lw t1, PS_MEPC(t0)
    lw a5, PS_FAULT_PC(t0)
    bne t1, a5, .Lreject
    li t2, REJECT_COUNT
    lw t1, PS_TRAPS(t0)
    li a5, 1
    bne t1, a5, .Lreject
    li t2, REJECT_CASE
    lw t1, PS_CASE(t0)
    li a5, CASE_REPLACEMENT
    beq t1, a5, .Lcase_valid
    li a5, CASE_ADDITION
    bne t1, a5, .Lreject
.Lcase_valid:
    li t2, REJECT_COUNT
    lw t1, PS_TOTAL_TRAPS(t0)
    lw a5, PS_CASE(t0)
    bne t1, a5, .Lreject
    li t2, REJECT_DISPATCH
    lw t1, PS_CASE(t0)
    li a5, CASE_REPLACEMENT
    beq t1, a5, .Lreplacement
    la a5, sram_addition
    j .Lselected
.Lreplacement:
    la a5, sram_replacement
.Lselected:
    lw t1, PS_ENTRY(t0)
    bne t1, a5, .Lreject
    sw a5, PS_DISPATCH(t0)

    li t2, REJECT_RULE
    csrr t1, pmpcfg0
    li a5, PATCH_NA4_CFG
    bne t1, a5, .Lreject
    csrr t1, pmpaddr0
    lw a5, PS_PMP_ADDR(t0)
    bne t1, a5, .Lreject
    lw t1, PS_FAULT_PC(t0)
    srli t1, t1, 2
    bne t1, a5, .Lreject
    li t2, REJECT_SECURITY
    csrr t1, 0x747
    bnez t1, .Lreject
    csrr t1, mtvec
    la a5, sram_trap_entry
    bne t1, a5, .Lreject
    csrr t1, mie
    bnez t1, .Lreject
    # This non-reentrant fixture requires MPP=M, MPRV=0 and MIE=0 at the trap.
    csrr t1, mstatus
    li a5, 0x21808
    and t1, t1, a5
    li a5, 0x1800
    bne t1, a5, .Lreject

    # Prefix completed, but neither ordinary output nor added output may have occurred.
    li t2, REJECT_PREFIX
    la a5, ordinary_output
    lw t1, 0(a5)
    bnez t1, .Lreject
    lw t1, PS_EXTRA(t0)
    bnez t1, .Lreject
    li t1, NATURAL_ROM_PREFIX_VALUE
    bne a0, t1, .Lreject
    li t2, REJECT_RESUME
    lw t1, PS_RESUME_PC(t0)
    lw a5, PS_FAULT_PC(t0)
    addi a5, a5, ROM_DISPLACED_BYTES
    bne t1, a5, .Lreject
    csrw mepc, t1
    lw a5, PS_DISPATCH(t0)
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    addi sp, sp, PATCH_CONTEXT_BYTES
    jr a5

.Lreject:
    sw t2, PS_ERROR(t0)
    la a5, sram_trap_failure
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    addi sp, sp, PATCH_CONTEXT_BYTES
    jr a5
.size sram_trap_entry, .-sram_trap_entry
.global sram_support_end
sram_support_end:

.section .mcu_sram.replacement, "ax", @progbits
.balign 2
.global sram_replacement
.global sram_replacement_begin
.type sram_replacement, @function
# Replace only ADDI's adjustment; replay the entire right-edge-straddling SRLI.
sram_replacement_begin:
sram_replacement:
    addi a0, a0, 34
    srli a5, a0, 8
    mret
.size sram_replacement, .-sram_replacement
.global sram_replacement_end
sram_replacement_end:

.section .mcu_sram.addition, "ax", @progbits
.balign 2
.global sram_addition
.global sram_addition_begin
.type sram_addition, @function
# a4 is dead until the first resumed ROM LUI; a5 is overwritten by replayed SRLI.
sram_addition_begin:
sram_addition:
    lui a4, %hi(patch_state + PS_EXTRA)
    li a5, ADDITIONAL_VALUE
    sw a5, %lo(patch_state + PS_EXTRA)(a4)
    c.addi a0, 17
    srli a5, a0, 8
    mret
.size sram_addition, .-sram_addition
.global sram_addition_end
sram_addition_end:
.option pop

# Reuse the existing linker's exact .bss collection, not an orphan .bss.* section.
.section .bss, "aw", @nobits
.balign 4
.global patch_state
.global patch_metadata_begin
.type patch_state, @object
patch_state:
patch_metadata_begin:
    .zero PATCH_METADATA_BYTES
.global patch_metadata_end
.global patch_observation_begin
patch_metadata_end:
patch_observation_begin:
    .zero PATCH_STATE_BYTES - PATCH_METADATA_BYTES
.global patch_observation_end
.global patch_state_end
patch_observation_end:
patch_state_end:
.size patch_state, .-patch_state
.global pmp_context_bytes
.equ pmp_context_bytes, PATCH_CONTEXT_BYTES

.section .note.GNU-stack, "", @progbits
