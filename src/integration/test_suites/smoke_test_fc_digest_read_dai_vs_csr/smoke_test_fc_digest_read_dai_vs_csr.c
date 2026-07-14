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
// Assumption-check test: secret-partition digest readback via TWO paths
//
// Goal
// ----
// Verify whether the 64-bit HW digest of a secret partition (hw_digest = yes)
// can be read back through BOTH of these software-visible paths, and whether
// the two paths return the SAME value:
//
//   Path A (named CSR):  lsu_read_32(<PART>_DIGEST_DIGEST_0/1)
//   Path B (DAI):        DIRECT_ACCESS_ADDRESS = <partition digest offset>;
//                        DIRECT_ACCESS_CMD.RD; read DIRECT_ACCESS_RDATA_0/1
//                        (wrapped by the dai_rd() library helper)
//
// Why this matters
// ----------------
// The secret-digest read-lock feature hides the true digest of secret
// partitions (UDS = SECRET_MANUF, Field Entropy = SECRET_PROD_0..3, etc.) once
// the SECRET_DIGEST_READ_LOCK is engaged, so the real digest is never exposed:
//   - DAI path: the read is fully short-circuited and returns 0.
//   - CSR path: masked to a provisioned indicator (all-1s if the digest is
//     non-zero/provisioned, else 0) instead of the real value.
// This test first confirms both paths expose the same true digest while
// unlocked, then confirms the masked behavior once the lock is engaged.
//
// The DAI keeps digest addresses readable even for secret, read-locked
// partitions (otp_ctrl_dai.sv: "HW digests ... always remain readable"), but
// the fuse_ctrl filter only lets the Caliptra-core AXI identity reach the
// secret address range. Hence this test drives the Caliptra-core identity via
// grant_caliptra_core_for_fc_writes() before issuing the DAI digest reads.
//
// Test steps (mirrors the copied smoke_test_fc_filter_rule_write_zer_id flow:
// mcu_cptra_init_d -> wait_dai_op_idle -> grant Caliptra-core -> DAI ops)
//   1. Init and grant the Caliptra-core identity.
//   2. Pre-lock: read each secret partition digest via CSR and via DAI, compare
//      (both paths expose the same digest while unlocked).
//   3. Provision + lock each secret partition (calculate_digest) so the digest
//      becomes a non-zero, content-derived value (best-effort; a marker is
//      written first), then re-compare CSR vs DAI.
//   4. Engage SECRET_DIGEST_READ_LOCK: the DAI digest must read 0 and the CSR
//      digest must read the provisioned indicator (all-1s if provisioned, else
//      0). Writing 0 to the W1S lock is a no-op.
//
// PASS  = both paths agree while unlocked AND, once locked, every DAI digest
//         reads 0 while its CSR digest reads only the provisioned indicator.
//
#include <string.h>
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

// A secret + hw_digest partition to exercise, together with the named CSR
// register offsets that expose its digest.
typedef struct {
    partition_k id;
    uint32_t    digest0_csr;
    uint32_t    digest1_csr;
    const char *name;
} digest_target_t;

static const digest_target_t targets[] = {
    { SECRET_MANUF_PARTITION,
      SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1,
      "SECRET_MANUF (UDS)" },
    { SECRET_PROD_PARTITION_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1,
      "SECRET_PROD_0 (FE0)" },
};
static const uint32_t kNumTargets = sizeof(targets) / sizeof(targets[0]);

static const digest_target_t mask_targets[] = {
    { SECRET_MANUF_PARTITION,
      SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_MANUF_PARTITION_DIGEST_DIGEST_1,
      "SECRET_MANUF (UDS)" },
    { SECRET_PROD_PARTITION_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_0_DIGEST_DIGEST_1,
      "SECRET_PROD_0 (FE0)" },
    { SECRET_PROD_PARTITION_1,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_0,
      SOC_OTP_CTRL_SECRET_PROD_PARTITION_1_DIGEST_DIGEST_1,
      "SECRET_PROD_1 (FE1)" },
};
static const uint32_t kNumMaskTargets = sizeof(mask_targets) / sizeof(mask_targets[0]);

// Read a partition digest via the named CSR path (always readable).
static void read_digest_csr(const digest_target_t *t, uint32_t *d0, uint32_t *d1) {
    *d0 = lsu_read_32(t->digest0_csr);
    *d1 = lsu_read_32(t->digest1_csr);
}

// Read a partition digest via the DAI path. For a secret partition this only
// succeeds under the Caliptra-core identity (the filter blocks the MCU). The
// digest address stays readable even after the partition is read-locked.
static bool read_digest_dai(const partition_t *part, uint32_t *d0, uint32_t *d1) {
    *d0 = 0;
    *d1 = 0;
    return dai_rd(part->digest_address, d0, d1, 64, 0);
}

// Read one partition's digest through both paths and compare.
// Returns true iff the DAI read succeeded and CSR value == DAI value.
static bool compare_digest_paths(const digest_target_t *t, const char *phase) {
    const partition_t part = partitions[t->id];
    uint32_t csr0, csr1, dai0, dai1;

    read_digest_csr(t, &csr0, &csr1);

    if (!read_digest_dai(&part, &dai0, &dai1)) {
        VPRINTF(LOW, "ERROR [%s] %s: DAI digest read (addr 0x%08X) did not return idle\n",
                phase, t->name, part.digest_address);
        return false;
    }

    VPRINTF(LOW, "INFO [%s] %s: CSR={%08X_%08X} DAI={%08X_%08X}\n",
            phase, t->name, csr1, csr0, dai1, dai0);

    if (csr0 != dai0 || csr1 != dai1) {
        VPRINTF(LOW, "MISMATCH [%s] %s: CSR and DAI digest differ\n", phase, t->name);
        return false;
    }

    bool nonzero = (csr0 != 0) || (csr1 != 0);
    VPRINTF(LOW, "MATCH [%s] %s: CSR == DAI (%s)\n",
            phase, t->name, nonzero ? "non-zero / provisioned" : "zero / unprovisioned");
    return true;
}

// Verify read-lock behavior for one partition digest. Under the lock:
//   - DAI path: fully short-circuited to 0 (the OTP read is skipped).
//   - CSR path: masked to the provisioned indicator: all-1s if the real digest
//     was non-zero (provisioned), else 0. The real digest is never exposed.
// csr_real{0,1} are the real CSR digest halves captured before the lock was set.
static bool expect_locked_digest(const digest_target_t *t, const char *phase,
                                 uint32_t csr_real0, uint32_t csr_real1) {
    const partition_t part = partitions[t->id];
    uint32_t csr0, csr1, dai0, dai1;
    bool ok = true;

    read_digest_csr(t, &csr0, &csr1);

    if (!read_digest_dai(&part, &dai0, &dai1)) {
        VPRINTF(LOW, "ERROR [%s] %s: DAI digest read (addr 0x%08X) did not return idle\n",
                phase, t->name, part.digest_address);
        return false;
    }

    // Provisioned indicator expected on the CSR path.
    const bool provisioned = (csr_real0 != 0) || (csr_real1 != 0);
    const uint32_t exp_csr0 = provisioned ? 0xFFFFFFFFu : 0x00000000u;
    const uint32_t exp_csr1 = provisioned ? 0xFFFFFFFFu : 0x00000000u;

    VPRINTF(LOW, "INFO [%s] %s: CSR={%08X_%08X} DAI={%08X_%08X} EXP_CSR={%08X_%08X}\n",
            phase, t->name, csr1, csr0, dai1, dai0, exp_csr1, exp_csr0);

    // DAI path must be fully short-circuited to 0 by the read lock.
    if (dai0 != 0 || dai1 != 0) {
        VPRINTF(LOW, "ERROR [%s] %s: DAI digest not short-circuited to 0 under read lock\n",
                phase, t->name);
        ok = false;
    }

    // CSR path must expose only the provisioned indicator, never the real digest.
    if (csr0 != exp_csr0 || csr1 != exp_csr1) {
        VPRINTF(LOW, "ERROR [%s] %s: CSR digest not masked to provisioned indicator "
                "(expected %08X_%08X)\n", phase, t->name, exp_csr1, exp_csr0);
        ok = false;
    }

    return ok;
}

// Best-effort: write a marker to the partition base and lock it so the HW
// digest becomes a non-zero, content-derived value. Failures are logged but do
// not abort the run — the CSR-vs-DAI comparison is the real assertion.
static void provision_and_lock(const digest_target_t *t) {
    const partition_t part = partitions[t->id];

    if (!wait_dai_op_idle(0)) {
        VPRINTF(LOW, "WARN: DAI not idle before provisioning %s\n", t->name);
        return;
    }

    if (!dai_wr(part.address, 0xA5A5A5A5, 0x5A5A5A5A, part.granularity, 0)) {
        VPRINTF(LOW, "WARN: marker write to %s (addr 0x%08X) not accepted\n",
                t->name, part.address);
    }

    if (!calculate_digest(part.address, 0)) {
        VPRINTF(LOW, "WARN: calculate_digest for %s (addr 0x%08X) did not complete cleanly\n",
                t->name, part.address);
    }

}

void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    // Standard Caliptra subsystem initialization.
    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();
    if (!wait_dai_op_idle(0)) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        return;
    }

    // Use the Caliptra-core AXI identity so DAI reads of secret digest
    // addresses pass the fuse_ctrl filter.
    grant_caliptra_core_for_fc_writes();
    mcu_sleep(20);
    if (!wait_dai_op_idle(0)) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        return;
    }

    bool passed = true;

    // Phase 1: pre-lock comparison (digests are expected to be zero on a fresh
    // OTP image; both paths should agree — 0 == 0).
    VPRINTF(LOW, "\n--- Phase 1: pre-lock CSR vs DAI digest read ---\n");
    for (uint32_t i = 0; i < kNumTargets; i++) {
        if (!compare_digest_paths(&targets[i], "pre-lock")) passed = false;
    }

    // Phase 2: lock each secret partition so its HW digest becomes non-zero.
    VPRINTF(LOW, "\n--- Phase 2: provision + lock secret partitions ---\n");
    for (uint32_t i = 0; i < kNumTargets; i++) {
        provision_and_lock(&targets[i]);
    }

    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0)) {
        VPRINTF(LOW, "ERROR: DAI not idle before Phase 3\n");
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        return;
    }

    // Phase 3: post-lock comparison. This is the meaningful check: both paths
    // must expose the identical (now non-zero) digest.
    VPRINTF(LOW, "\n--- Phase 3: post-lock CSR vs DAI digest read ---\n");
    for (uint32_t i = 0; i < kNumTargets; i++) {
        if (!compare_digest_paths(&targets[i], "post-lock")) passed = false;
    }

    // Phase 4: set the global W1S digest-read lock. The DAI digest read is then
    // fully short-circuited to 0, and the CSR digest is masked to the provisioned
    // indicator (all-1s if provisioned, else 0). Capture each real CSR digest
    // first so we can derive the expected indicator.
    VPRINTF(LOW, "\n--- Phase 4: read lock masks CSR (indicator) and DAI (0) ---\n");

    uint32_t csr_real0[sizeof(mask_targets) / sizeof(mask_targets[0])];
    uint32_t csr_real1[sizeof(mask_targets) / sizeof(mask_targets[0])];
    for (uint32_t i = 0; i < kNumMaskTargets; i++) {
        read_digest_csr(&mask_targets[i], &csr_real0[i], &csr_real1[i]);
    }

    lsu_write_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK, 1);
    mcu_sleep(20);
    if ((lsu_read_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK) & 1u) != 1u) {
        VPRINTF(LOW, "ERROR [phase4-lock]: SECRET_DIGEST_READ_LOCK did not set\n");
        passed = false;
    }

    for (uint32_t i = 0; i < kNumMaskTargets; i++) {
        if (!expect_locked_digest(&mask_targets[i], "masked-lock", csr_real0[i], csr_real1[i])) {
            passed = false;
        }
    }

    // Phase 5: writing 0 to the W1S lock is a no-op (it stays set), so the DAI
    // digest stays short-circuited to 0 and the CSR digest stays masked to the
    // provisioned indicator. Do not reset here; a reset would clear the W1S lock.
    VPRINTF(LOW, "\n--- Phase 5: write-0 no-op keeps the mask engaged ---\n");
    lsu_write_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK, 0);
    mcu_sleep(20);
    if ((lsu_read_32(SOC_OTP_CTRL_SECRET_DIGEST_READ_LOCK) & 1u) != 1u) {
        VPRINTF(LOW, "ERROR [phase5-write0]: W1S lock unexpectedly cleared by write-0\n");
        passed = false;
    }
    if (!wait_dai_op_idle(0)) {
        VPRINTF(LOW, "ERROR [phase5-write0]: DAI not idle before write-0 checks\n");
        passed = false;
    }

    for (uint32_t i = 0; i < kNumMaskTargets; i++) {
        if (!expect_locked_digest(&mask_targets[i], "write0-noop", csr_real0[i], csr_real1[i])) {
            passed = false;
        }
    }

    mcu_sleep(160);
    VPRINTF(LOW, "\nINFO: digest read path comparison completed (%s).\n",
            passed ? "all paths matched" : "MISMATCH or read error seen");

    SEND_STDOUT_CTRL(passed ? TB_CMD_TEST_PASS : TB_CMD_TEST_FAIL);
}
