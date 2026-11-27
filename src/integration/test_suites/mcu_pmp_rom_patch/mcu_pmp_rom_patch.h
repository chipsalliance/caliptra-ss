// SPDX-License-Identifier: Apache-2.0
#ifndef MCU_PMP_ROM_PATCH_H
#define MCU_PMP_ROM_PATCH_H

#define NATURAL_ROM_INPUT 0x4b4b4b5a
#define NATURAL_ROM_PREFIX_VALUE 0x11111100
#define NATURAL_ROM_OUTPUT 0x11111111
#define NATURAL_ROM_RESULT 0x11222222
#define REPLACEMENT_OUTPUT 0x11111122
#define REPLACEMENT_RESULT 0x11222233
#define ADDITIONAL_VALUE 0x33333333
#define ROM_FUNCTION_BYTES 28
#define ROM_PATCH_OFFSET 10
#define ROM_RESUME_OFFSET 16
#define ROM_DISPLACED_BYTES 6
#define ROM_INTERCEPT_BYTES 4
#define PROBE_NA4_CFG 0x11
#define PATCH_NA4_CFG 0x91

#define CASE_BASELINE 0
#define CASE_REPLACEMENT 1
#define CASE_ADDITION 2

// RV32 layout shared by the SRAM assembler and typed C harness.
#define PS_CASE 0
#define PS_FAULT_PC 4
#define PS_RESUME_PC 8
#define PS_PMP_ADDR 12
#define PS_ENTRY 16
#define PS_TRAPS 20
#define PS_TOTAL_TRAPS 24
#define PS_CAUSE 28
#define PS_MEPC 32
#define PS_DISPATCH 36
#define PS_ERROR 40
#define PS_EXTRA 44
#define PATCH_METADATA_BYTES 20
#define PATCH_STATE_BYTES 48
#define PATCH_CONTEXT_BYTES 16

#define REJECT_CAUSE 1
#define REJECT_PC 2
#define REJECT_COUNT 3
#define REJECT_CASE 4
#define REJECT_DISPATCH 5
#define REJECT_RULE 6
#define REJECT_SECURITY 7
#define REJECT_PREFIX 8
#define REJECT_RESUME 9

#ifndef PMP_PATCH_ASM
#include <stddef.h>
#include <stdint.h>

#if !defined(__riscv) || __riscv_xlen != 32 || !defined(__riscv_compressed)
#error "This target-specific replay requires RV32 with the C extension"
#endif
#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "This target-specific opcode manifest requires little-endian memory"
#endif

// Mutable patch metadata and common observations; no state is added to the ROM work.
typedef struct {
    uint32_t active_case;
    uint32_t fault_pc;
    uint32_t resume_pc;
    uint32_t pmp_address;
    uint32_t configured_entry;
    uint32_t trap_count;
    uint32_t total_trap_count;
    uint32_t last_mcause;
    uint32_t last_mepc;
    uint32_t last_dispatch;
    uint32_t error;
    uint32_t additional_output;
} pmp_patch_state_t;

_Static_assert(sizeof(uintptr_t) == 4 && sizeof(pmp_patch_state_t) == PATCH_STATE_BYTES, "RV32 patch state size");
#define CHECK_STATE_OFFSET(member, offset) _Static_assert(offsetof(pmp_patch_state_t, member) == offset, "patch state offset: " #member)
CHECK_STATE_OFFSET(active_case, PS_CASE);
CHECK_STATE_OFFSET(fault_pc, PS_FAULT_PC);
CHECK_STATE_OFFSET(resume_pc, PS_RESUME_PC);
CHECK_STATE_OFFSET(pmp_address, PS_PMP_ADDR);
CHECK_STATE_OFFSET(configured_entry, PS_ENTRY);
CHECK_STATE_OFFSET(trap_count, PS_TRAPS);
CHECK_STATE_OFFSET(total_trap_count, PS_TOTAL_TRAPS);
CHECK_STATE_OFFSET(last_mcause, PS_CAUSE);
CHECK_STATE_OFFSET(last_mepc, PS_MEPC);
CHECK_STATE_OFFSET(last_dispatch, PS_DISPATCH);
CHECK_STATE_OFFSET(error, PS_ERROR);
CHECK_STATE_OFFSET(additional_output, PS_EXTRA);
#undef CHECK_STATE_OFFSET

extern volatile pmp_patch_state_t patch_state;
extern volatile uint32_t ordinary_output;
uint32_t ordinary_rom_work(uint32_t input);

#endif
#endif
