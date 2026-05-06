//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//********************************************************************************
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Raw (unhashed) CPTRA_SS_MANUF_TO_PROD_TOKEN from test_unlock_token.hjson:
// 0x51c001f2c721179d5d8318f4f622abb6
static const uint32_t manuf_to_prod_token[4] = {
    0xf622abb6, 0x5d8318f4, 0xc721179d, 0x51c001f2
};

/**
 * This test validates PROD_DEBUG_UNLOCK_MANUF_PARTITION:
 *   1. Starts in MANUF state (set via vmem init with --lc-state 16).
 *   2. Provisions a few words in PKS_0 (first key) and PKS_7 (last key).
 *   3. Locks the partition with a SW digest.
 *   4. Transitions from MANUF to PROD, resets, verifies state.
 *   5. Verifies writes to the partition are blocked in PROD state.
 *   6. Zeroizes marker (disables ECC), then data, then digest.
 *   7. Resets and confirms the controller comes up cleanly.
 *
 *   The partition has ECC (integrity: true), so the zeroization marker
 *   must be zeroized before the data words to avoid ECC errors.
 */
void prod_debug_unlock_prov_zeroize(void) {
    uint32_t r_data[2];
    const partition_t part = partitions[PROD_DEBUG_UNLOCK_MANUF_PARTITION];

    // =========================================================
    // Phase 1: Verify we are in MANUF state
    // =========================================================
    VPRINTF(LOW, "=== Phase 1: Verify MANUF state ===\n");
    if (!check_lc_state("MANUF", MANUF)) goto fail;
    VPRINTF(LOW, "Confirmed MANUF state.\n");

    // =========================================================
    // Phase 2: Provision first and last PKS entries
    // =========================================================
    VPRINTF(LOW, "=== Phase 2: Provisioning PKS_0 and PKS_7 ===\n");

    // Write a few words to PKS_0 (first key).
    dai_wr(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0, 0xA5A5A5A5, 0, part.granularity, 0);
    dai_rd(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0, &r_data[0], &r_data[1], part.granularity, 0);
    if (r_data[0] != 0xA5A5A5A5) {
        VPRINTF(LOW, "ERROR: PKS_0 read 0x%08X != expected 0xA5A5A5A5\n", r_data[0]);
        goto fail;
    }

    dai_wr(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0 + 4, 0x12345678, 0, part.granularity, 0);
    dai_rd(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0 + 4, &r_data[0], &r_data[1], part.granularity, 0);
    if (r_data[0] != 0x12345678) {
        VPRINTF(LOW, "ERROR: PKS_0+4 read 0x%08X != expected 0x12345678\n", r_data[0]);
        goto fail;
    }

    // Write a few words to PKS_7 (last key).
    dai_wr(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7, 0xDEADBEEF, 0, part.granularity, 0);
    dai_rd(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7, &r_data[0], &r_data[1], part.granularity, 0);
    if (r_data[0] != 0xDEADBEEF) {
        VPRINTF(LOW, "ERROR: PKS_7 read 0x%08X != expected 0xDEADBEEF\n", r_data[0]);
        goto fail;
    }

    dai_wr(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7 + 4, 0xCAFEBABE, 0, part.granularity, 0);
    dai_rd(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7 + 4, &r_data[0], &r_data[1], part.granularity, 0);
    if (r_data[0] != 0xCAFEBABE) {
        VPRINTF(LOW, "ERROR: PKS_7+4 read 0x%08X != expected 0xCAFEBABE\n", r_data[0]);
        goto fail;
    }
    VPRINTF(LOW, "PKS_0 and PKS_7 provisioned and verified.\n");

    // =========================================================
    // Phase 3: Lock partition with SW digest
    // =========================================================
    VPRINTF(LOW, "=== Phase 3: Locking partition with SW digest ===\n");

    dai_wr(part.digest_address, 0xDEADBEEF, 0xCAFEBABE, 64, 0);
    memset(r_data, 0, sizeof(r_data));
    dai_rd(part.digest_address, &r_data[0], &r_data[1], 64, 0);
    if (r_data[0] != 0xDEADBEEF || r_data[1] != 0xCAFEBABE) {
        VPRINTF(LOW, "ERROR: Digest read-back mismatch\n");
        goto fail;
    }
    VPRINTF(LOW, "Partition digest written and verified.\n");

    // Reset to activate the write lock.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // =========================================================
    // Phase 4: Transition from MANUF to PROD
    // =========================================================
    VPRINTF(LOW, "=== Phase 4: Transitioning MANUF -> PROD ===\n");

    transition_state(PROD, manuf_to_prod_token, false);

    // Reset to reflect the new LC state.
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    if (!check_lc_state("PROD", PROD)) goto fail;
    VPRINTF(LOW, "Successfully transitioned to PROD state.\n");

    // =========================================================
    // Phase 5: Verify writes are blocked in PROD state
    // =========================================================
    VPRINTF(LOW, "=== Phase 5: Verifying writes blocked in PROD ===\n");

    dai_wr(part.address, 0xFF, 0, part.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    VPRINTF(LOW, "Write correctly rejected in PROD state.\n");

    // =========================================================
    // Phase 6: Zeroize the partition in PROD state
    //   Order: marker first (disables ECC) -> data -> digest
    // =========================================================
    VPRINTF(LOW, "=== Phase 6: Zeroizing partition in PROD state ===\n");

    // Zeroize marker field first to disable ECC on this partition.
    if (!dai_zer(part.zer_address, 64, 0, false)) {
        VPRINTF(LOW, "ERROR: Failed to zeroize marker field\n");
        goto fail;
    }
    VPRINTF(LOW, "Zeroization marker cleared (ECC disabled).\n");

    // Zeroize the written fuse data entries.
    if (!dai_zer(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0, part.granularity, 0, false)) {
        VPRINTF(LOW, "ERROR: Failed to zeroize PKS_0\n");
        goto fail;
    }
    if (!dai_zer(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_0 + 4, part.granularity, 0, false)) {
        VPRINTF(LOW, "ERROR: Failed to zeroize PKS_0+4\n");
        goto fail;
    }
    if (!dai_zer(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7, part.granularity, 0, false)) {
        VPRINTF(LOW, "ERROR: Failed to zeroize PKS_7\n");
        goto fail;
    }
    if (!dai_zer(CPTRA_SS_PROD_DEBUG_UNLOCK_PKS_7 + 4, part.granularity, 0, false)) {
        VPRINTF(LOW, "ERROR: Failed to zeroize PKS_7+4\n");
        goto fail;
    }

    // Zeroize digest field.
    if (!dai_zer(part.digest_address, 64, 0, false)) {
        VPRINTF(LOW, "ERROR: Failed to zeroize digest field\n");
        goto fail;
    }
    VPRINTF(LOW, "Partition zeroized.\n");

    // =========================================================
    // Phase 7: Reset and verify clean startup after zeroization
    // =========================================================
    VPRINTF(LOW, "=== Phase 7: Post-zeroize reset and verify ===\n");

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Verify the zeroization marker reads as all-ones.
    memset(r_data, 0, sizeof(r_data));
    dai_rd(part.zer_address, &r_data[0], &r_data[1], 64, 0);
    if (r_data[0] != 0xFFFFFFFF || r_data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: Zeroization marker not all-ones after reset\n");
        goto fail;
    }
    VPRINTF(LOW, "Zeroization marker verified after reset.\n");

    VPRINTF(LOW, "=== TEST PASSED ===\n");
    return;

fail:
    handle_error("prod_debug_unlock_prov_zeroize FAILED");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    // LC state starts in MANUF via vmem init (--lc-state 16).
    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    prod_debug_unlock_prov_zeroize();

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    SEND_STDOUT_CTRL(0xff);
}
