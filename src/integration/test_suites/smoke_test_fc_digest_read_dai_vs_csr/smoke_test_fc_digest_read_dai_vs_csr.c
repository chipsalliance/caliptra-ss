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
// SECRET_DIGEST_READ_LOCK test (read lock ONLY).
//
// Exercises the W1S SECRET_DIGEST_READ_LOCK CSR, which hides secret partition HW
// digests from software once set:
//   - Named CSR path: masked to the provisioned indicator (all-1s if the digest
//     is provisioned/non-zero, else 0), never the real digest.
//   - DAI path: short-circuited to 0.
//
// Partitions are provisioned + locked via the VMEM (secret_partitions_locked.hjson)
// so their digests are non-zero at boot; SECRET_PROD_PARTITION_3 is left
// unprovisioned so the 0-indicator case is also covered. One digest per secret
// partition is checked.
//
// PASS = baseline exposes the real digest on both paths AND, once the read lock is
//        set, every DAI digest reads 0 while every CSR digest reads only the
//        provisioned indicator (all-1s for provisioned, 0 for unprovisioned).
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

// Baseline: both paths must expose the SAME real digest (non-zero for a
// provisioned partition, zero for an unprovisioned one).
static void check_baseline(uint32_t i) {
    const digest_target_t *t = &secret_targets[i];
    uint32_t csr0, csr1, dai0, dai1;

    read_digest_csr(t, &csr0, &csr1);
    if (!read_digest_dai(t, &dai0, &dai1)) {
        handle_error("ERROR [baseline] %s: DAI digest read did not return idle\n", t->name);
    }

    VPRINTF(LOW, "INFO [baseline] %s: CSR={%08X_%08X} DAI={%08X_%08X}\n",
            t->name, csr1, csr0, dai1, dai0);

    if (csr0 != dai0 || csr1 != dai1) {
        handle_error("ERROR [baseline] %s: CSR and DAI digest differ\n", t->name);
    }
    const bool nonzero = (csr0 != 0) || (csr1 != 0);
    if (t->expect_provisioned && !nonzero) {
        handle_error("ERROR [baseline] %s: expected provisioned digest but read 0\n", t->name);
    }
    if (!t->expect_provisioned && nonzero) {
        handle_error("ERROR [baseline] %s: expected unprovisioned (0) digest but read non-zero\n", t->name);
    }
}

// Under the read lock: DAI digest must read 0, and the CSR digest must read only
// the provisioned indicator (all-1s for provisioned, 0 for unprovisioned).
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

void main(void) {
    VPRINTF(LOW, "==================================================\n"
                 "FC secret digest read lock test (read lock only)\n"
                 "==================================================\n\n");

    mcu_cptra_init_d();
    if (!wait_dai_op_idle(0)) {
        handle_error("ERROR: DAI not idle after init\n");
    }

    // ---------------------------------------------------------------------
    // Phase 1: baseline. Both paths expose the same real digest. DAI secret
    // reads use the Caliptra-core AXI identity so they pass the fuse_ctrl filter.
    // ---------------------------------------------------------------------
    VPRINTF(LOW, "\n--- Phase 1: baseline CSR == DAI == real digest ---\n");
    grant_caliptra_core_for_fc_writes();
    for (uint32_t i = 0; i < NUM_SECRET_TARGETS; i++) {
        check_baseline(i);
    }
    revoke_grant_mcu_for_fc_writes();

    // ---------------------------------------------------------------------
    // Phase 2: engage SECRET_DIGEST_READ_LOCK (W1S), written under the default
    // MCU identity. DAI digest -> 0, CSR digest -> provisioned indicator. A
    // write of 0 is a no-op.
    // ---------------------------------------------------------------------
    VPRINTF(LOW, "\n--- Phase 2: SECRET_DIGEST_READ_LOCK hides the digest ---\n");
    lsu_write_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK, 1);
    mcu_sleep(20);
    if ((lsu_read_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK) & 1u) != 1u) {
        handle_error("ERROR [read-lock]: SECRET_DIGEST_READ_LOCK did not set\n");
    }
    lsu_write_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK, 0); // W1S: write-0 is a no-op
    mcu_sleep(20);
    if ((lsu_read_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK) & 1u) != 1u) {
        handle_error("ERROR [read-lock]: W1S lock unexpectedly cleared by write-0\n");
    }
    if (!wait_dai_op_idle(0)) {
        handle_error("ERROR [read-lock]: DAI not idle after engaging read lock\n");
    }
    grant_caliptra_core_for_fc_writes();
    for (uint32_t i = 0; i < NUM_SECRET_TARGETS; i++) {
        check_hidden(i, "read-lock");
    }
    revoke_grant_mcu_for_fc_writes();

    mcu_sleep(160);
    VPRINTF(LOW, "\nINFO: secret digest read lock test completed (PASS).\n");

    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
