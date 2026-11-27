// SPDX-License-Identifier: Apache-2.0
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "caliptra_ss_lib.h"
#include "mcu_pmp_rom_patch.h"
#include <stdint.h>

#define SRAM_BASE 0x21c00000u
#define SRAM_EXEC_BYTES 0x8000u

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

extern char sram_patch_begin[], sram_trap_entry[], sram_support_end[];
extern char sram_replacement[], sram_replacement_end[];
extern char sram_addition[], sram_addition_end[];
extern char patch_metadata_begin[], patch_metadata_end[];
extern char patch_observation_begin[], patch_observation_end[], patch_state_end[];
extern char _mcu_sram_end[];

void sram_trap_failure(void) __attribute__((section(".mcu_sram.failure"), noinline, noreturn));

// Keep patch-dependent rejection in SRAM; reuse only generic ROM reporting services.
void sram_trap_failure(void) {
    handle_error("PMP: SRAM rejection error=%u case=%u traps=%u total=%u cause=%x pc=%x dispatch=%x\n",
                 patch_state.error, patch_state.active_case, patch_state.trap_count, patch_state.total_trap_count,
                 patch_state.last_mcause, patch_state.last_mepc, patch_state.last_dispatch);
}

// Read a possibly halfword-aligned 32-bit instruction without an unaligned load.
static uint32_t instruction32(uintptr_t pc) {
    volatile const uint16_t *halves = (volatile const uint16_t *)pc;
    return (uint32_t)halves[0] | ((uint32_t)halves[1] << 16);
}

// Encode the existing ordinary suffix's LUI a4 for the final linked data address.
static uint32_t address_lui(uintptr_t address) {
    return ((address + 0x800u) & 0xfffff000u) | 0x737u;
}

// Encode SW rs2,lo12(address)(a4), paired with address_lui().
static uint32_t address_store(uintptr_t address, uint32_t rs2) {
    return 0x72023u | (rs2 << 20) | ((address & 0xfe0u) << 20) | ((address & 0x1fu) << 7);
}

// Bind only the observed GCC12.2 RV32C sequence, allowing normal symbol/data relocation.
static void check_rom_image(void) {
    static const uint16_t prefix[] = {0x67b7, 0x5a5a, 0x8793, 0xa5a7, 0x8d3d, 0x0545, 0x5793, 0x0085};
    uintptr_t entry = (uintptr_t)ordinary_rom_work;
    volatile const uint16_t *code = (volatile const uint16_t *)entry;

    if (entry < 0x80000000u || entry > 0x80040000u - ROM_FUNCTION_BYTES ||
        ((entry + ROM_PATCH_OFFSET) & (ROM_INTERCEPT_BYTES - 1u)) != 0) {
        handle_error("PMP: unsupported natural ROM bounds/alignment entry=%x\n", entry);
    }
    for (uint32_t i = 0; i < sizeof(prefix) / sizeof(prefix[0]); ++i) {
        if (code[i] != prefix[i]) {
            handle_error("PMP: unsupported ROM opcode at offset=%u got=%x expected=%x\n", 2 * i, code[i], prefix[i]);
        }
    }
    // a4 is overwritten before use at resume; both suffix address instructions must still target ordinary_output.
    if (instruction32(entry + 16) != address_lui((uintptr_t)&ordinary_output) ||
        instruction32(entry + 20) != address_store((uintptr_t)&ordinary_output, 10) ||
        code[12] != 0x953e || code[13] != 0x8082) {
        handle_error("PMP: unsupported ordinary suffix or relocated output instructions\n");
    }
}

// Check every payload instruction, enabled SRAM bounds, and the complete state allocation.
static void check_sram_image(void) {
    uintptr_t begin = (uintptr_t)sram_patch_begin;
    uintptr_t support_end = (uintptr_t)sram_support_end;
    uintptr_t replacement = (uintptr_t)sram_replacement;
    uintptr_t replacement_end = (uintptr_t)sram_replacement_end;
    uintptr_t addition = (uintptr_t)sram_addition;
    uintptr_t addition_end = (uintptr_t)sram_addition_end;
    uintptr_t failure = (uintptr_t)sram_trap_failure;
    uintptr_t end = (uintptr_t)_mcu_sram_end;
    uintptr_t state = (uintptr_t)&patch_state;
    uintptr_t output = (uintptr_t)&ordinary_output;
    uintptr_t extra_address = (uintptr_t)&patch_state.additional_output;
    volatile const uint16_t *add_code = (volatile const uint16_t *)addition;

    if (begin != SRAM_BASE || (uintptr_t)sram_trap_entry != begin || (begin & 3u) ||
        support_end <= begin || replacement < support_end || (replacement & 1u) || replacement_end - replacement != 12 ||
        addition < replacement_end || (addition & 1u) || addition_end - addition != 26 ||
        failure < addition_end || end <= failure || end > SRAM_BASE + SRAM_EXEC_BYTES) {
        handle_error("PMP: invalid SRAM support/payload layout\n");
    }
    if (state < 0x50000000u || state > 0x50004000u - PATCH_STATE_BYTES || (state & 3u) ||
        (uintptr_t)patch_state_end != state + PATCH_STATE_BYTES || (uintptr_t)patch_metadata_begin != state ||
        (uintptr_t)patch_metadata_end - (uintptr_t)patch_metadata_begin != PATCH_METADATA_BYTES ||
        (uintptr_t)patch_observation_begin != (uintptr_t)patch_metadata_end ||
        (uintptr_t)patch_observation_end != (uintptr_t)patch_state_end ||
        output < 0x50000000u || output > 0x50004000u - sizeof(ordinary_output) || (output & 3u) ||
        (output >= state && output < (uintptr_t)patch_state_end)) {
        handle_error("PMP: invalid DCCM patch state allocation\n");
    }
    if (instruction32(replacement) != 0x02250513u || instruction32(replacement + 4) != 0x00855793u ||
        instruction32(replacement + 8) != 0x30200073u ||
        instruction32(addition) != address_lui(extra_address) || instruction32(addition + 4) != 0x333337b7u ||
        instruction32(addition + 8) != 0x33378793u || instruction32(addition + 12) != address_store(extra_address, 15) ||
        add_code[8] != 0x0545 || instruction32(addition + 18) != 0x00855793u || instruction32(addition + 22) != 0x30200073u) {
        handle_error("PMP: SRAM payload preload/opcode guard failed\n");
    }
}

// Report all SRAM code, gaps, mutable data and the borrowed success-path context.
static void report_footprint(void) {
    uint32_t total = (uintptr_t)_mcu_sram_end - (uintptr_t)sram_patch_begin;
    uint32_t support = (uintptr_t)sram_support_end - (uintptr_t)sram_patch_begin;
    uint32_t replacement = (uintptr_t)sram_replacement_end - (uintptr_t)sram_replacement;
    uint32_t addition = (uintptr_t)sram_addition_end - (uintptr_t)sram_addition;
    uint32_t failure = (uintptr_t)_mcu_sram_end - (uintptr_t)sram_trap_failure;

    VPRINTF(LOW, "PMP: SRAM bytes total=%u support=%u replacement=%u addition=%u rejection_and_tail=%u gaps=%u\n",
            total, support, replacement, addition, failure, total - support - replacement - addition - failure);
    VPRINTF(LOW, "PMP: DCCM state=%u metadata=%u observations=%u borrowed_context=%u; diagnostics use existing printf stack\n",
            PATCH_STATE_BYTES, PATCH_METADATA_BYTES, PATCH_STATE_BYTES - PATCH_METADATA_BYTES, PATCH_CONTEXT_BYTES);
    VPRINTF(LOW, "PMP: ROM deny=%u bytes; displaced=2 instructions/%u bytes; SRAM payload instructions replacement=3 addition=7\n",
            ROM_INTERCEPT_BYTES, ROM_DISPLACED_BYTES);
}

// Reject changes to target-specific patch metadata, regardless of final ROM symbol placement.
static void check_metadata(void) {
    uintptr_t fault_pc = (uintptr_t)ordinary_rom_work + ROM_PATCH_OFFSET;
    if (patch_state.fault_pc != fault_pc || patch_state.resume_pc != (uintptr_t)ordinary_rom_work + ROM_RESUME_OFFSET ||
        patch_state.pmp_address != (fault_pc >> 2)) {
        handle_error("PMP: target metadata changed\n");
    }
}

// Observe protection and trap configuration before/after each normal ROM call.
static void check_mode(uint32_t armed) {
    uint32_t mseccfg;
    uint32_t expected_cfg = armed ? PATCH_NA4_CFG : 0;
    uint32_t expected_address = armed ? patch_state.pmp_address : 0;

    __asm__ volatile ("csrr %0, 0x747" : "=r"(mseccfg));
    if (mseccfg != 0 || csr_read_pmpcfg0() != expected_cfg || csr_read_pmpaddr0() != expected_address ||
        csr_read_mtvec() != (uintptr_t)sram_trap_entry || csr_read_mie() != 0 || (csr_read_mstatus() & 0x20008u) != 0) {
        handle_error("PMP: mode changed case=%u sec=%x cfg=%x addr=%x mtvec=%x\n",
                     patch_state.active_case, mseccfg, csr_read_pmpcfg0(), csr_read_pmpaddr0(), csr_read_mtvec());
    }
    check_metadata();
}

// Reject a coarser grain or missing NA4 before any irreversible rule installation.
static void check_na4_capability(void) {
    uint32_t mseccfg;
    uint32_t grain_probe;
    uint32_t address = ((uintptr_t)ordinary_rom_work & ~(ROM_INTERCEPT_BYTES - 1u)) >> 2;

    __asm__ volatile ("csrr %0, 0x747" : "=r"(mseccfg));
    if (mseccfg != 0 || csr_read_pmpcfg0() != 0) {
        handle_error("PMP: require fixture MSECCFG/PMPCFG0 zero, got %x/%x\n", mseccfg, csr_read_pmpcfg0());
    }

    // Machine ISA 2.7.1.1: OFF/all-ones readback discovers the lowest address bit.
    csr_write_pmpcfg0(0);
    csr_write_pmpaddr0(0xffffffffu);
    grain_probe = csr_read_pmpaddr0();
    if (!(grain_probe & 1u)) {
        handle_error("PMP: four-byte grain unavailable, pmpaddr0=%x\n", grain_probe);
    }
    csr_write_pmpaddr0(address);
    csr_write_pmpcfg0(PROBE_NA4_CFG);
    if (csr_read_pmpcfg0() != PROBE_NA4_CFG || csr_read_pmpaddr0() != address) {
        handle_error("PMP: NA4 probe readback failed cfg=%x addr=%x\n", csr_read_pmpcfg0(), csr_read_pmpaddr0());
    }
    // The probe never set L; restore OFF before the baseline, not a locked rule.
    csr_write_pmpcfg0(0);
    csr_write_pmpaddr0(0);
    __asm__ volatile ("csrr %0, 0x747" : "=r"(mseccfg));
    if (mseccfg != 0 || csr_read_pmpcfg0() != 0 || csr_read_pmpaddr0() != 0) {
        handle_error("PMP: capability probe cleanup failed\n");
    }
    VPRINTF(LOW, "PMP: capability readback grain=%u NA4=%x pmpaddr_probe=%x; rule remains OFF\n",
            ROM_INTERCEPT_BYTES, PROBE_NA4_CFG, grain_probe);
}

// Clear per-call observations only; retain target metadata, cumulative traps and the rule.
static void reset_case(uint32_t scenario) {
    patch_state.trap_count = 0;
    patch_state.last_mcause = 0;
    patch_state.last_mepc = 0;
    patch_state.last_dispatch = 0;
    patch_state.error = 0;
    patch_state.additional_output = 0;
    ordinary_output = 0;
    patch_state.configured_entry = scenario == CASE_REPLACEMENT ? (uintptr_t)sram_replacement :
                                   scenario == CASE_ADDITION ? (uintptr_t)sram_addition : 0;
    patch_state.active_case = scenario;
}

// Call only the ordinary ROM function and check all expected effects outside that function.
static void run_case(uint32_t scenario) {
    uint32_t armed = scenario != CASE_BASELINE;
    uint32_t is_replacement = scenario == CASE_REPLACEMENT;
    uint32_t expected_output = is_replacement ? REPLACEMENT_OUTPUT : NATURAL_ROM_OUTPUT;
    uint32_t expected_result = is_replacement ? REPLACEMENT_RESULT : NATURAL_ROM_RESULT;
    uint32_t expected_extra = scenario == CASE_ADDITION ? ADDITIONAL_VALUE : 0;
    uint32_t result;

    if (scenario > CASE_ADDITION || patch_state.total_trap_count != (armed ? scenario - 1 : 0)) {
        handle_error("PMP: invalid case sequence case=%u total=%u\n", scenario, patch_state.total_trap_count);
    }
    reset_case(scenario);
    check_rom_image();
    check_mode(armed);
    VPRINTF(LOW, "PMP: starting case=%u ROM=%x input=%x dispatch=%x expected_output/result=%x/%x extra=%x\n",
            scenario, (uintptr_t)ordinary_rom_work, NATURAL_ROM_INPUT, patch_state.configured_entry,
            expected_output, expected_result, expected_extra);
    result = ordinary_rom_work(NATURAL_ROM_INPUT);
    check_mode(armed);
    check_rom_image();
    if (patch_state.error != 0 || patch_state.trap_count != armed || patch_state.total_trap_count != scenario ||
        patch_state.last_mcause != armed || patch_state.last_mepc != (armed ? patch_state.fault_pc : 0) ||
        patch_state.last_dispatch != patch_state.configured_entry || patch_state.additional_output != expected_extra ||
        ordinary_output != expected_output || result != expected_result) {
        handle_error("PMP: FAIL case=%u error=%u traps=%u total=%u cause=%x pc=%x dispatch=%x output=%x result=%x extra=%x\n",
                     scenario, patch_state.error, patch_state.trap_count, patch_state.total_trap_count,
                     patch_state.last_mcause, patch_state.last_mepc, patch_state.last_dispatch, ordinary_output,
                     result, patch_state.additional_output);
    }
    VPRINTF(LOW, "PMP: case=%u PASS traps=%u total=%u cause=%x pc=%x dispatch=%x output=%x result=%x extra=%x\n",
            scenario, patch_state.trap_count, patch_state.total_trap_count, patch_state.last_mcause, patch_state.last_mepc,
            patch_state.last_dispatch, ordinary_output, result, patch_state.additional_output);
}

// Install patch support outside the ordinary payload, then reuse one ROM image in all cases.
void main(void) {
    if (!(lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON) & MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK)) {
        VPRINTF(LOW, "PMP: enable SRAM execution through the Caliptra fixture\n");
        mcu_cptra_init_d(.cfg_mcu_fw_sram_exec_reg_size=true, .mcu_fw_sram_exec_reg_size=SRAM_EXEC_BYTES);
        mcu_mci_poll_exec_lock();
        mcu_mci_req_reset();
        while (1);
    }

    csr_write_mie(0);
    csr_clr_bits_mstatus(8);
    if ((csr_read_mstatus() & 0x20000u) != 0) {
        handle_error("PMP: require fixture MPRV zero\n");
    }
    check_rom_image();
    check_sram_image();
    check_na4_capability();
    patch_state.fault_pc = (uintptr_t)ordinary_rom_work + ROM_PATCH_OFFSET;
    patch_state.resume_pc = (uintptr_t)ordinary_rom_work + ROM_RESUME_OFFSET;
    patch_state.pmp_address = patch_state.fault_pc >> 2;
    patch_state.total_trap_count = 0;
    reset_case(CASE_BASELINE);
    __asm__ volatile ("fence.i" ::: "memory");
    csr_write_mtvec((uintptr_t)sram_trap_entry);
    VPRINTF(LOW, "PMP: natural ROM=%x fault/deny=%x..%x displaced=%u resume=%x SRAM_handler=%x\n",
            (uintptr_t)ordinary_rom_work, patch_state.fault_pc, patch_state.fault_pc + ROM_INTERCEPT_BYTES - 1,
            ROM_DISPLACED_BYTES, patch_state.resume_pc, (uintptr_t)sram_trap_entry);
    report_footprint();
    run_case(CASE_BASELINE);

    csr_write_pmpaddr0(patch_state.pmp_address);
    csr_write_pmpcfg0(PATCH_NA4_CFG);
    __asm__ volatile ("fence.i" ::: "memory");
    // Reject actual clear attempts without setting RLB or changing this rule between cases.
    csr_write_pmpcfg0(0);
    csr_write_pmpaddr0(0);
    check_mode(1);
    __asm__ volatile ("fence.i" ::: "memory");
    VPRINTF(LOW, "PMP: locked NA4 cfg=%x addr=%x deny=%x..%x; starting replacement then addition\n",
            csr_read_pmpcfg0(), csr_read_pmpaddr0(), patch_state.fault_pc, patch_state.fault_pc + ROM_INTERCEPT_BYTES - 1);
    run_case(CASE_REPLACEMENT);
    run_case(CASE_ADDITION);
    check_sram_image();
    check_mode(1);
    if (patch_state.total_trap_count != 2 || patch_state.active_case != CASE_ADDITION) {
        handle_error("PMP: incomplete final case state\n");
    }
    VPRINTF(LOW, "PMP: PASS baseline/replacement/addition complete; total_traps=%u original_output=%x result=%x extra=%x\n",
            patch_state.total_trap_count, ordinary_output, NATURAL_ROM_RESULT, patch_state.additional_output);
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    while (1);
}
