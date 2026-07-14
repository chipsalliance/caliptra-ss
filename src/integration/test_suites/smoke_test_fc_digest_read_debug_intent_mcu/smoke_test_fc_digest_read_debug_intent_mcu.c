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
//
// MCU debug-intent secret HW-digest hiding test.
//
// The fuse controller senses the secret partitions in hardware during boot
// (before this test runs) while SS_DEBUG_INTENT_MCU is still 0, so the real
// digests are captured. The MCU then writes the W1S SS_DEBUG_INTENT_MCU register
// to assert debug intent. Because that register is only writable before
// SS_CONFIG_DONE_STICKY is set, it is written at the very start of main() (before
// mcu_cptra_init_d asserts config done). Once debug intent is asserted:
//   - Named CSR path: secret HW digests are masked to the provisioned indicator
//     (all-1s if provisioned/non-zero, else 0), never the real digest.
//   - DAI path: the digest read is short-circuited to 0.
//
// Then the SECRET_DIGEST_READ_LOCK is ALSO engaged (both mechanisms set at once)
// and the same digest checks are repeated, to prove the two hiding mechanisms do
// not break each other when combined.
//
// Partitions are provisioned + locked via the VMEM (secret_partitions_locked.hjson);
// SECRET_PROD_PARTITION_3 is left unprovisioned so the 0-indicator case is also
// covered. One digest per secret partition is checked. The all-1s indicator for a
// provisioned partition proves its real (non-zero) digest was sensed before being
// masked.
//
// PASS = under debug intent (and again with the read lock also set) every DAI
//        digest reads 0 and every CSR digest reads only the provisioned
//        indicator (all-1s for provisioned, 0 for unprovisioned).
//
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// One secret + hw_digest partition to exercise, with the named-CSR register
// offsets that expose its digest. expect_provisioned selects the masked value:
// all-1s when the VMEM provisions/locks the partition, 0 when it is left
// unprovisioned.
typedef struct {
    partition_k id;
    uint32_t    digest0_csr;
    uint32_t    digest1_csr;
    bool        expect_provisioned;
    const char *name;
} digest_target_t;

static const digest_target_t secret_targets[] = {
    { SECRET_MANUF_PARTITION,
      SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1, true,  "SECRET_MANUF (UDS)" },
    { SECRET_PROD_PARTITION_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1, true,  "SECRET_PROD_0 (FE0)" },
    { SECRET_PROD_PARTITION_1,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1, true,  "SECRET_PROD_1 (FE1)" },
    { SECRET_PROD_PARTITION_2,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_2_DIGEST_DIGEST_1, true,  "SECRET_PROD_2 (FE2)" },
    { VENDOR_SECRET_PROD_PARTITION,
      SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_VENDOR_SECRET_PROD_PARTITION_DIGEST_DIGEST_1, true, "VENDOR_SECRET_PROD" },
    // Left unprovisioned by the VMEM: digest stays 0, so the masked indicator is 0.
    { SECRET_PROD_PARTITION_3,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_3_DIGEST_DIGEST_1, false, "SECRET_PROD_3 (unprovisioned)" },
};
#define NUM_SECRET_TARGETS (sizeof(secret_targets) / sizeof(secret_targets[0]))

static void read_digest_csr(const digest_target_t *t, uint32_t *d0, uint32_t *d1) {
    *d0 = lsu_read_32(t->digest0_csr);
    *d1 = lsu_read_32(t->digest1_csr);
}

// DAI read of a secret partition digest (needs the Caliptra-core identity; the
// digest address stays readable, though the read may be short-circuited to 0).
static bool read_digest_dai(const digest_target_t *t, uint32_t *d0, uint32_t *d1) {
    const partition_t part = partitions[t->id];
    *d0 = 0;
    *d1 = 0;
    return dai_rd(part.digest_address, d0, d1, 64, 0);
}

// Under a digest-hiding mechanism: DAI digest must read 0, and the CSR digest
// must read only the provisioned indicator (all-1s for provisioned, 0 for
// unprovisioned).
static void check_hidden(uint32_t i, const char *phase) {
    const digest_target_t *t = &secret_targets[i];
    uint32_t csr0, csr1, dai0, dai1;

    read_digest_csr(t, &csr0, &csr1);
    if (!read_digest_dai(t, &dai0, &dai1)) {
        handle_error("ERROR [%s] %s: DAI digest read did not return idle\n", phase, t->name);
    }

    const uint32_t exp_csr = t->expect_provisioned ? 0xFFFFFFFFu : 0x00000000u;

    VPRINTF(LOW, "INFO [%s] %s: CSR={%08X_%08X} DAI={%08X_%08X} EXP_CSR=%08X\n",
            phase, t->name, csr1, csr0, dai1, dai0, exp_csr);

    if (dai0 != 0 || dai1 != 0) {
        handle_error("ERROR [%s] %s: DAI digest not short-circuited to 0\n", phase, t->name);
    }
    if (csr0 != exp_csr || csr1 != exp_csr) {
        handle_error("ERROR [%s] %s: CSR digest not the provisioned indicator (exp %08X)\n",
                     phase, t->name, exp_csr);
    }
}

static void run_hidden_checks(const char *phase) {
    grant_caliptra_core_for_fc_writes();
    for (uint32_t i = 0; i < NUM_SECRET_TARGETS; i++) {
        check_hidden(i, phase);
    }
    revoke_grant_mcu_for_fc_writes();
}

void main(void) {
    VPRINTF(LOW, "==================================================\n"
                 "FC secret digest hiding: MCU debug intent (+ read lock)\n"
                 "==================================================\n\n");

    // Assert debug intent via the MCU register (W1S, MCU-only). It must be
    // written before SS_CONFIG_DONE_STICKY is set, hence before mcu_cptra_init_d.
    // The partitions were already sensed in HW during boot (register was 0 then),
    // so their real digests are captured before this masks them.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT_MCU, 1);
    mcu_sleep(20);
    if ((lsu_read_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT_MCU) &
         MCI_REG_SS_DEBUG_INTENT_MCU_DEBUG_INTENT_MASK) == 0) {
        handle_error("ERROR [dbg-intent]: SS_DEBUG_INTENT_MCU did not set\n");
    }

    // W1S: writing 0 must be a no-op while the register is still writable (before
    // config done). Confirm the bit stays set.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT_MCU, 0);
    mcu_sleep(20);
    if ((lsu_read_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT_MCU) &
         MCI_REG_SS_DEBUG_INTENT_MCU_DEBUG_INTENT_MASK) == 0) {
        handle_error("ERROR [dbg-intent]: SS_DEBUG_INTENT_MCU (W1S) unexpectedly cleared by write-0\n");
    }

    mcu_cptra_init_d();
    if (!wait_dai_op_idle(0)) {
        handle_error("ERROR: DAI not idle after init\n");
    }

    // ---------------------------------------------------------------------
    // Phase 1: debug intent is active (asserted above). DAI digest -> 0 and CSR
    // digest -> provisioned indicator (all-1s provisioned, 0 unprovisioned). DAI
    // secret reads use the Caliptra-core AXI identity so they pass the fuse_ctrl
    // filter. The all-1s result proves the provisioned digest was really sensed.
    // ---------------------------------------------------------------------
    VPRINTF(LOW, "\n--- Phase 1: MCU debug intent hides the digest ---\n");
    run_hidden_checks("dbg-intent");

    // ---------------------------------------------------------------------
    // Phase 2: ALSO engage SECRET_DIGEST_READ_LOCK (W1S) so both hiding
    // mechanisms are set at once. Repeat the digest checks to confirm the logic
    // is not broken when both are active. Write-0 is a no-op.
    // ---------------------------------------------------------------------
    VPRINTF(LOW, "\n--- Phase 2: read lock ALSO set (both mechanisms active) ---\n");
    lsu_write_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK, 1);
    mcu_sleep(20);
    if ((lsu_read_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK) & 1u) != 1u) {
        handle_error("ERROR [both]: SECRET_DIGEST_READ_LOCK did not set\n");
    }
    lsu_write_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK, 0); // W1S: write-0 is a no-op
    mcu_sleep(20);
    if ((lsu_read_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK) & 1u) != 1u) {
        handle_error("ERROR [both]: W1S lock unexpectedly cleared by write-0\n");
    }
    if (!wait_dai_op_idle(0)) {
        handle_error("ERROR [both]: DAI not idle after engaging read lock\n");
    }
    run_hidden_checks("both");

    mcu_sleep(160);
    VPRINTF(LOW, "\nINFO: MCU debug-intent digest hiding test completed (PASS).\n");

    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
