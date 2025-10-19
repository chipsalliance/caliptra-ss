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

bool try_to_zeroize_secret_partition(const char        *name,
                                     const partition_t *part,
                                     uint32_t           exp_status) {
    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0)) return false;

    if (!dai_zer(part->address, part->granularity, exp_status, false)) {
        VPRINTF(LOW, "ERROR: Unexpected status zeroizing %s partition\n", name);
        return false;
    }

    return true;
}

bool try_to_zeroize_secret_partitions(uint32_t exp_status) {
    const partition_t hw_part_uds = partitions[SECRET_MANUF_PARTITION];
    const partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];
    const partition_t hw_part_fe1 = partitions[SECRET_PROD_PARTITION_1];
    const partition_t hw_part_fe2 = partitions[SECRET_PROD_PARTITION_2];
    const partition_t hw_part_fe3 = partitions[SECRET_PROD_PARTITION_3];

    if (!try_to_zeroize_secret_partition("UDS", &hw_part_uds, exp_status))
        return false;
#ifndef SHORT_TEST
    if (!try_to_zeroize_secret_partition("FE0", &hw_part_fe0, exp_status))
        return false;
    if (!try_to_zeroize_secret_partition("FE1", &hw_part_fe1, exp_status))
        return false;
    if (!try_to_zeroize_secret_partition("FE2", &hw_part_fe2, exp_status))
        return false;
    if (!try_to_zeroize_secret_partition("FE3", &hw_part_fe3, exp_status))
        return false;
#endif

    return true;
}

bool invalid_secret_zeroization(void) {
    VPRINTF(LOW, "INFO: Starting invalid secret zeroization test...\n");

    if (!try_to_zeroize_secret_partitions(OTP_CTRL_STATUS_DAI_ERROR_MASK))
        return false;

    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0)) return false;

    VPRINTF(LOW, "INFO: Invalid secret zeroization steps completed.\n");
    return true;
}

bool valid_secret_zeroization(void) {
    VPRINTF(LOW, "INFO: Starting valid secret zeroization test...\n");

    if (!try_to_zeroize_secret_partitions(0))
        return false;

    VPRINTF(LOW, "INFO: Valid secret zeroization test completed.\n");
    return true;
}

void provision_partition(const char *name,
                         const partition_t *part,
                         const uint32_t data[2]) {
    VPRINTF(LOW, "INFO: Writing %s partition...\n", name);
    dai_wr(part->address, data[0], data[1], part->granularity, 0);

    VPRINTF(LOW, "INFO: Calculating digest for %s partition...\n", name);
    calculate_digest(part->address, 0);

#ifndef SHORT_TEST
    VPRINTF(LOW, "INFO: Resetting to activate %s partition lock...\n", name);
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
#endif
}

void secret_prov(void) {
    VPRINTF(LOW, "INFO: Starting secret provisioning...\n");

    uint32_t data[2] = { 0xA5A5A5A5, 0x5A5A5A5A };

    // Provision each secret partition
    provision_partition("UDS", &partitions[SECRET_MANUF_PARTITION], data);
#ifndef SHORT_TEST
    provision_partition("FE0", &partitions[SECRET_PROD_PARTITION_0], data);
    provision_partition("FE1", &partitions[SECRET_PROD_PARTITION_1], data);
    provision_partition("FE2", &partitions[SECRET_PROD_PARTITION_2], data);
    provision_partition("FE3", &partitions[SECRET_PROD_PARTITION_3], data);
#endif

    VPRINTF(LOW, "INFO: Secret provisioning completed.\n");
}

// Run num_nops nop instructions as a sleep loop.
void sleep(unsigned num_nops)
{
    for (unsigned i = 0; i < num_nops; i++) {
        __asm__ volatile ("nop");
    }
}

void body(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();

    VPRINTF(LOW, "INFO: Granting MCU access to fuse controller...\n");
    grant_caliptra_core_for_fc_writes();

    sleep(20);
    if (!wait_dai_op_idle(0)) return;

    VPRINTF(LOW, "INFO: Starting secret provisioning sequence...\n");
    secret_prov();
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    sleep(20);

    VPRINTF(LOW, "INFO: Revoking MCU access to fuse controller...\n");
    revoke_grant_mcu_for_fc_writes();

    sleep(20);

    VPRINTF(LOW, "INFO: Starting invalid secret zeroization test...\n");
    if (!invalid_secret_zeroization()) return;
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    sleep(20);

    VPRINTF(LOW, "INFO: Granting MCU access again for valid zeroization...\n");
    grant_caliptra_core_for_fc_writes();

    VPRINTF(LOW, "INFO: Starting NO PPD invalid secret zeroization test...\n");
    if (!invalid_secret_zeroization()) return;
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    sleep(20);

    VPRINTF(LOW, "INFO: Starting valid secret zeroization test...\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
    if (!valid_secret_zeroization()) return;
    VPRINTF(LOW, "\n\n------------------------------\n\n");
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    body();

    sleep(160);
    VPRINTF(LOW, "INFO: MCU Caliptra Boot sequence completed.\n");
    SEND_STDOUT_CTRL(0xff);
}
