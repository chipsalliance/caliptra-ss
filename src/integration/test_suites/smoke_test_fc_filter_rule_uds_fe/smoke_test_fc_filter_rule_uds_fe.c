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

// #define SHORT_TEST

// Use dai_zer to request zeroization of the given partition. If
// exp_success is true, we expect this to complete with status zero.
// If exp_success is false, we expect the DAI_ERROR field to be set in
// otp_ctrl's status register.
//
// If the check passes and the operation completes without an error,
// perform a reset to bring everything back up again.
//
// Return true if all exit codes were as expected.
bool try_to_zeroize_secret_partition(const char        *name,
                                     const partition_t *part,
                                     bool               exp_success) {

    uint32_t exp_status = exp_success ? 0 : OTP_CTRL_STATUS_DAI_ERROR_MASK;

    if (!dai_zer(part->address, part->granularity, exp_status, false)) {
        VPRINTF(LOW,
                "ERROR: Unexpected status zeroizing %s partition\n", name);
        return false;
    }

    if (exp_status == 0) {
        // We've successfully zeroized the partition, so we inject a
        // reset to start again. Note that zeroization will have
        // messed up the ECC data in the partition (since the contents
        // are now all-ones), which will cause all the partition
        // errors to be set, plus dai_error and lci_error.
        uint32_t exp_post_rst_status = (((1 << NUM_PARTITIONS) - 1) |
                                        OTP_CTRL_STATUS_DAI_ERROR_MASK |
                                        OTP_CTRL_STATUS_LCI_ERROR_MASK);

        reset_fc_lcc_rtl();
        if (!wait_dai_op_idle(exp_post_rst_status)) return false;
    }

    return true;
}

// Use try_to_zeroize_secret_partition to request zeroization of each
// secret partition (where exp_success tracks whether it is expected
// to work).
//
// Return true if all partitions behaved as expected.
bool try_to_zeroize_secret_partitions(bool exp_success) {
    const partition_t hw_part_uds = partitions[SECRET_MANUF_PARTITION];
    const partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];
    const partition_t hw_part_fe1 = partitions[SECRET_PROD_PARTITION_1];
    const partition_t hw_part_fe2 = partitions[SECRET_PROD_PARTITION_2];
    const partition_t hw_part_fe3 = partitions[SECRET_PROD_PARTITION_3];

    if (!try_to_zeroize_secret_partition("UDS", &hw_part_uds, exp_success))
        return false;
#ifndef SHORT_TEST
    if (!try_to_zeroize_secret_partition("FE0", &hw_part_fe0, exp_success))
        return false;
    if (!try_to_zeroize_secret_partition("FE1", &hw_part_fe1, exp_success))
        return false;
    if (!try_to_zeroize_secret_partition("FE2", &hw_part_fe2, exp_success))
        return false;
    if (!try_to_zeroize_secret_partition("FE3", &hw_part_fe3, exp_success))
        return false;
#endif

    return true;
}

// Write data to the first entry of the given partition, then
// calculate a digest for the partition. Return true if every step
// succeeds.
bool provision_partition(const char *name,
                         const partition_t *part,
                         const uint32_t data[2]) {
    VPRINTF(LOW, "INFO: Writing %s partition...\n", name);
    if (!dai_wr(part->address, data[0], data[1], part->granularity, 0))
        return false;

    VPRINTF(LOW, "INFO: Calculating digest for %s partition...\n", name);
    return calculate_digest(part->address, 0);
}

// Write data to provision each secret partition. Return true if this
// succeeds.
bool secret_prov(void) {
    VPRINTF(LOW, "INFO: Starting secret provisioning...\n");

    uint32_t data[2] = { 0xA5A5A5A5, 0x5A5A5A5A };

    if (!provision_partition("UDS", &partitions[SECRET_MANUF_PARTITION], data))
        return false;
#ifndef SHORT_TEST
    if (!provision_partition("FE0", &partitions[SECRET_PROD_PARTITION_0], data))
        return false;
    if (!provision_partition("FE1", &partitions[SECRET_PROD_PARTITION_1], data))
        return false;
    if (!provision_partition("FE2", &partitions[SECRET_PROD_PARTITION_2], data))
        return false;
    if (!provision_partition("FE3", &partitions[SECRET_PROD_PARTITION_3], data))
        return false;
#endif

    VPRINTF(LOW, "INFO: Resetting to activate partition locks\n");
    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0))
        return false;

    VPRINTF(LOW, "INFO: Secret provisioning completed.\n");
    return true;
}

bool body(void) {
    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();

    VPRINTF(LOW, "INFO: Granting MCU access to fuse controller...\n");
    grant_caliptra_core_for_fc_writes();

    mcu_sleep(20);
    if (!wait_dai_op_idle(0)) return false;

    VPRINTF(LOW, "INFO: Starting secret provisioning sequence...\n");
    if (!secret_prov()) return false;
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    mcu_sleep(20);

    VPRINTF(LOW, "INFO: Revoking MCU access to fuse controller...\n");
    revoke_grant_mcu_for_fc_writes();

    mcu_sleep(20);

    VPRINTF(LOW, "INFO: Starting invalid secret zeroization test...\n");
    if (!try_to_zeroize_secret_partitions(false)) return false;
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    mcu_sleep(20);

    VPRINTF(LOW, "INFO: Granting MCU access again for valid zeroization...\n");
    grant_caliptra_core_for_fc_writes();

    VPRINTF(LOW, "INFO: Starting NO PPD invalid secret zeroization test...\n");
    if (!try_to_zeroize_secret_partitions(false)) return false;
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    mcu_sleep(20);

    VPRINTF(LOW, "INFO: Starting valid secret zeroization test...\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
    if (!try_to_zeroize_secret_partitions(true)) return false;
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    return true;
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    bool passed = body();

    mcu_sleep(160);
    VPRINTF(LOW, "INFO: MCU Caliptra Boot sequence completed.\n");
    SEND_STDOUT_CTRL(passed ? TB_CMD_TEST_PASS : TB_CMD_TEST_FAIL);
}
