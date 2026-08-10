// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Smoke test: ordinary DCCM stores/loads must keep working with the DCCM
// write-readback check both enabled and disabled.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#define MFDC_CSR                            (0x7f9)
#define MFDC_DCCM_WR_READBACK_DISABLE_MASK  (0x80u)  // bit 7, "dwrd"

// DCCM has 4 banks selected by address bits [3:2]. The buffer is 16-byte
// aligned so word indices 0..3 of each group land in banks 0..3 in turn.
#define WORDS_PER_GROUP 4

static volatile uint32_t dccm_buf[64] __attribute__ ((section(".dccm"), aligned(16))) = {0};
static volatile uint8_t  dccm_bytes[16] __attribute__ ((section(".dccm"), aligned(16))) = {0};

static const uint32_t patterns[8] = {
    0x12345678u, 0xdeadbeefu, 0x00000000u, 0xffffffffu,
    0xa5a5a5a5u, 0x5a5a5a5au, 0x00000001u, 0x80000000u
};

// Two groups far enough apart to also exercise distinct DCCM rows, mirroring
// the offset spread of the upstream test.
static const uint32_t group_base[2] = {0, 32};

static uint32_t read_mfdc(void) {
    uint32_t mfdc;

    __asm__ volatile ("csrr %0, %1"
                      : "=r" (mfdc)
                      : "i" (MFDC_CSR)
                      : );

    return mfdc;
}

static uint8_t set_dccm_wr_readback_disable(void) {
    uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;

    __asm__ volatile ("csrs %0, %1"
                      :
                      : "i" (MFDC_CSR), "r" (mask)
                      : );

    if (!(read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK)) {
        VPRINTF(FATAL, "MCU DCCM RDBK: FAIL dwrd did not set, mfdc = 0x%x\n", read_mfdc());
        return 1;
    }

    return 0;
}

static uint8_t clear_dccm_wr_readback_disable(void) {
    uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;

    __asm__ volatile ("csrc %0, %1"
                      :
                      : "i" (MFDC_CSR), "r" (mask)
                      : );

    if (read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK) {
        VPRINTF(FATAL, "MCU DCCM RDBK: FAIL dwrd did not clear, mfdc = 0x%x\n", read_mfdc());
        return 1;
    }

    return 0;
}

// Word stores across all DCCM banks, then the byte/half-word read-modify-write
// store path, which takes a different route through the store buffer than the
// aligned word stores above.
static uint8_t check_dccm_writes(const char *phase) {
    uint32_t val;
    uint32_t idx;
    int g, i;

    VPRINTF(LOW, "MCU DCCM RDBK: checking DCCM writes (%s)\n", phase);

    for (g = 0; g < 2; g++) {
        for (i = 0; i < WORDS_PER_GROUP; i++) {
            dccm_buf[group_base[g] + i] = patterns[(g * WORDS_PER_GROUP) + i];
        }
    }

    for (g = 0; g < 2; g++) {
        for (i = 0; i < WORDS_PER_GROUP; i++) {
            idx = group_base[g] + i;
            val = dccm_buf[idx];
            if (val != patterns[(g * WORDS_PER_GROUP) + i]) {
                VPRINTF(FATAL, "MCU DCCM RDBK: FAIL word idx %d (%s) wrote 0x%x read 0x%x\n",
                        idx, phase, patterns[(g * WORDS_PER_GROUP) + i], val);
                return 1;
            }
        }
    }

    dccm_bytes[0] = 0x5au;
    dccm_bytes[8] = 0xa5u;

    if (dccm_bytes[0] != 0x5au) {
        VPRINTF(FATAL, "MCU DCCM RDBK: FAIL byte 0 (%s) read 0x%x\n", phase, dccm_bytes[0]);
        return 1;
    }
    if (dccm_bytes[8] != 0xa5u) {
        VPRINTF(FATAL, "MCU DCCM RDBK: FAIL byte 8 (%s) read 0x%x\n", phase, dccm_bytes[8]);
        return 1;
    }

    VPRINTF(LOW, "MCU DCCM RDBK: DCCM writes OK (%s)\n", phase);

    return 0;
}

uint8_t main(void) {
    uint32_t mfdc;

    VPRINTF(LOW, "MCU DCCM RDBK: write-readback enable/disable smoke test\n");

    // --- 1. Reset default: dwrd clear, i.e. the check is enabled ---
    mfdc = read_mfdc();
    VPRINTF(LOW, "MCU DCCM RDBK: mfdc = 0x%x (expect bit 7 clear)\n", mfdc);
    if (mfdc & MFDC_DCCM_WR_READBACK_DISABLE_MASK) {
        VPRINTF(FATAL, "MCU DCCM RDBK: FAIL dwrd set out of reset\n");
        return 1;
    }

    // --- 2. DCCM traffic with the check enabled ---
    if (check_dccm_writes("readback enabled") != 0) {
        return 2;
    }

    // --- 3. Disable the check and repeat ---
    if (set_dccm_wr_readback_disable() != 0) {
        return 3;
    }
    if (check_dccm_writes("readback disabled") != 0) {
        return 4;
    }

    // --- 4. Re-enable the check and repeat once more ---
    if (clear_dccm_wr_readback_disable() != 0) {
        return 5;
    }
    if (check_dccm_writes("readback re-enabled") != 0) {
        return 6;
    }

    VPRINTF(LOW, "MCU DCCM RDBK: PASS\n");

    mcu_cptra_init_d();
    mcu_cptra_poll_mb_ready();

    // return status is treated as an 'exit' code by mcu_crt0
    // 0-value indicates success, non-zero is error
    return 0;
}
