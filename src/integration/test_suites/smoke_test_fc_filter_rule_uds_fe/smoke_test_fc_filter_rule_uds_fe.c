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

#define SHORT_TEST

void invalid_secret_zeroization(void) {
    uint32_t data[2];

    const partition_t hw_part_uds = partitions[SECRET_MANUF_PARTITION];
    const partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];
    const partition_t hw_part_fe1 = partitions[SECRET_PROD_PARTITION_1];
    const partition_t hw_part_fe2 = partitions[SECRET_PROD_PARTITION_2];
    const partition_t hw_part_fe3 = partitions[SECRET_PROD_PARTITION_3];

    VPRINTF(LOW, "INFO: Starting invalid secret zeroization test...\n");

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    VPRINTF(LOW, "INFO: Attempting to zeroize UDS partition (expected to fail)...\n");
    dai_zer(hw_part_uds.address, &data[0], &data[1], hw_part_uds.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
#ifndef SHORT_TEST
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    VPRINTF(LOW, "INFO: Attempting to zeroize FE0 partition (expected to fail)...\n");
    dai_zer(hw_part_fe0.address, &data[0], &data[1], hw_part_fe0.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    VPRINTF(LOW, "INFO: Attempting to zeroize FE1 partition (expected to fail)...\n");
    dai_zer(hw_part_fe1.address, &data[0], &data[1], hw_part_fe1.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    VPRINTF(LOW, "INFO: Attempting to zeroize FE2 partition (expected to fail)...\n");
    dai_zer(hw_part_fe2.address, &data[0], &data[1], hw_part_fe2.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
    VPRINTF(LOW, "INFO: Attempting to zeroize FE3 partition (expected to fail)...\n");
    dai_zer(hw_part_fe3.address, &data[0], &data[1], hw_part_fe3.granularity, OTP_CTRL_STATUS_DAI_ERROR_MASK);
#endif
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: Invalid secret zeroization steps completed.\n");
}




void valid_secret_zeroization(void) {
    uint32_t data[2];

    const partition_t hw_part_uds = partitions[SECRET_MANUF_PARTITION];
    const partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];
    const partition_t hw_part_fe1 = partitions[SECRET_PROD_PARTITION_1];
    const partition_t hw_part_fe2 = partitions[SECRET_PROD_PARTITION_2];
    const partition_t hw_part_fe3 = partitions[SECRET_PROD_PARTITION_3];

    VPRINTF(LOW, "INFO: Starting valid secret zeroization test...\n");

    dai_zer(hw_part_uds.address, &data[0], &data[1], hw_part_uds.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: UDS fuse is not zeroized\n");
        goto epilogue;
    } else {
        VPRINTF(LOW, "PASS: UDS fuse successfully zeroized\n");
    }
#ifndef SHORT_TEST
    dai_zer(hw_part_fe0.address, &data[0], &data[1], hw_part_fe0.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: FE0 fuse is not zeroized\n");
        goto epilogue;
    } else {
        VPRINTF(LOW, "PASS: FE0 fuse successfully zeroized\n");
    }

    dai_zer(hw_part_fe1.address, &data[0], &data[1], hw_part_fe1.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: FE1 fuse is not zeroized\n");
        goto epilogue;
    } else {
        VPRINTF(LOW, "PASS: FE1 fuse successfully zeroized\n");
    }

    dai_zer(hw_part_fe2.address, &data[0], &data[1], hw_part_fe2.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: FE2 fuse is not zeroized\n");
        goto epilogue;
    } else {
        VPRINTF(LOW, "PASS: FE2 fuse successfully zeroized\n");
    }

    dai_zer(hw_part_fe3.address, &data[0], &data[1], hw_part_fe3.granularity, 0);
    if (data[0] != 0xFFFFFFFF || data[1] != 0xFFFFFFFF) {
        VPRINTF(LOW, "ERROR: FE3 fuse is not zeroized\n");
        goto epilogue;
    } else {
        VPRINTF(LOW, "PASS: FE3 fuse successfully zeroized\n");
    }
#endif
epilogue:
    VPRINTF(LOW, "INFO: Valid secret zeroization test completed.\n");
}

void secret_prov(void) {
    VPRINTF(LOW, "INFO: Starting secret provisioning...\n");

    uint32_t data0 = 0xA5A5A5A5;
    uint32_t data1 = 0x5A5A5A5A;

    const partition_t hw_part_uds = partitions[SECRET_MANUF_PARTITION];
    const partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];
    const partition_t hw_part_fe1 = partitions[SECRET_PROD_PARTITION_1];
    const partition_t hw_part_fe2 = partitions[SECRET_PROD_PARTITION_2];
    const partition_t hw_part_fe3 = partitions[SECRET_PROD_PARTITION_3];

    // Provision UDS
    VPRINTF(LOW, "INFO: Writing UDS partition...\n");
    dai_wr(hw_part_uds.address, data0, data1, hw_part_uds.granularity, 0);

    VPRINTF(LOW, "INFO: Calculating digest for UDS partition...\n");
    calculate_digest(hw_part_uds.address, 0);
#ifndef SHORT_TEST
    VPRINTF(LOW, "INFO: Resetting to activate UDS partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Provision FE0
    VPRINTF(LOW, "INFO: Writing FE0 partition...\n");
    dai_wr(hw_part_fe0.address, data0, data1, hw_part_fe0.granularity, 0);

    VPRINTF(LOW, "INFO: Calculating digest for FE0 partition...\n");
    calculate_digest(hw_part_fe0.address, 0);

    VPRINTF(LOW, "INFO: Resetting to activate FE0 partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Provision FE1
    VPRINTF(LOW, "INFO: Writing FE1 partition...\n");
    dai_wr(hw_part_fe1.address, data0, data1, hw_part_fe1.granularity, 0);

    VPRINTF(LOW, "INFO: Calculating digest for FE1 partition...\n");
    calculate_digest(hw_part_fe1.address, 0);

    VPRINTF(LOW, "INFO: Resetting to activate FE1 partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Provision FE2
    VPRINTF(LOW, "INFO: Writing FE2 partition...\n");
    dai_wr(hw_part_fe2.address, data0, data1, hw_part_fe2.granularity, 0);

    VPRINTF(LOW, "INFO: Calculating digest for FE2 partition...\n");
    calculate_digest(hw_part_fe2.address, 0);

    VPRINTF(LOW, "INFO: Resetting to activate FE2 partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);

    // Provision FE3
    VPRINTF(LOW, "INFO: Writing FE3 partition...\n");
    dai_wr(hw_part_fe3.address, data0, data1, hw_part_fe3.granularity, 0);

    VPRINTF(LOW, "INFO: Calculating digest for FE3 partition...\n");
    calculate_digest(hw_part_fe3.address, 0);

    VPRINTF(LOW, "INFO: Resetting to activate FE3 partition lock...\n");
    reset_fc_lcc_rtl();
    wait_dai_op_idle(0);
#endif
    VPRINTF(LOW, "INFO: Secret provisioning completed.\n");
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();

    VPRINTF(LOW, "INFO: Granting MCU access to fuse controller...\n");
    grant_caliptra_core_for_fc_writes();

    for (uint8_t ii = 0; ii < 20; ii++) {
        __asm__ volatile ("nop"); // Sleep loop
    }

    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: Starting secret provisioning sequence...\n");
    secret_prov();
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    // for (uint8_t ii = 0; ii < 20; ii++) {
    //     __asm__ volatile ("nop"); // Sleep loop
    // }

    // VPRINTF(LOW, "INFO: Revoking MCU access to fuse controller...\n");
    // revoke_grant_mcu_for_fc_writes();

    // for (uint8_t ii = 0; ii < 20; ii++) {
    //     __asm__ volatile ("nop"); // Sleep loop
    // }

    // VPRINTF(LOW, "INFO: Starting invalid secret zeroization test...\n");
    // invalid_secret_zeroization();
    // VPRINTF(LOW, "\n\n------------------------------\n\n");

    // for (uint8_t ii = 0; ii < 20; ii++) {
    //     __asm__ volatile ("nop"); // Sleep loop
    // }

    VPRINTF(LOW, "INFO: Granting MCU access again for valid zeroization...\n");
    grant_caliptra_core_for_fc_writes();

    VPRINTF(LOW, "INFO: Starting NO PPD invalid secret zeroization test...\n");
    invalid_secret_zeroization();
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    for (uint8_t ii = 0; ii < 20; ii++) {
        __asm__ volatile ("nop"); // Sleep loop
    }

    VPRINTF(LOW, "INFO: Starting valid secret zeroization test...\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_ZEROIZATION);
    valid_secret_zeroization();
    VPRINTF(LOW, "\n\n------------------------------\n\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Final sleep loop
    }

    VPRINTF(LOW, "INFO: MCU Caliptra Boot sequence completed.\n");
    SEND_STDOUT_CTRL(0xff);
}
