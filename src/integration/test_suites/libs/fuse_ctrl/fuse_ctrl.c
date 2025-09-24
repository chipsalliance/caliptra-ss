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
//

#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "soc_address_map.h"
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "riscv_hw_if.h"
#include "fuse_ctrl_mmap.h"
#include "fuse_ctrl.h"

void grant_mcu_for_fc_writes(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FORCE_FC_AWUSER_MCU);
    VPRINTF(LOW, "LCC & Fuse_CTRL is under MCU_LSU_AXI_USER!\n");
    for (uint16_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void revoke_grant_mcu_for_fc_writes(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_RELEASE_AWUSER);
    VPRINTF(LOW, "MCU_LSU_AXI_USER forcing signal is released!\n");
    for (uint16_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void grant_caliptra_core_for_fc_writes(void) {
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FORCE_FC_AWUSER_CPTR_CORE);
    VPRINTF(LOW, "LCC & Fuse_CTRL is under CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER!\n");
    for (uint16_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void wait_dai_op_idle(uint32_t status_mask) {
    uint32_t status;
    uint32_t dai_idle;
    uint32_t check_pending;

    const uint32_t error_mask = OTP_CTRL_STATUS_DAI_IDLE_MASK - 1;

    VPRINTF(LOW, "DEBUG: Waiting for DAI to become idle...\n");
    do {
        status = lsu_read_32(SOC_OTP_CTRL_STATUS);
        dai_idle = (status >> OTP_CTRL_STATUS_DAI_IDLE_LOW) & 0x1;
        check_pending = (status >> OTP_CTRL_STATUS_CHECK_PENDING_LOW) & 0x1;
        
    } while ((!dai_idle || check_pending) && ((status & error_mask) != error_mask));
    VPRINTF(LOW, "%08X\n", status);
    // Clear the IDLE bit from the status value
    status &= ((((uint32_t)1) << (OTP_CTRL_STATUS_DAI_IDLE_LOW - 1)) - 1);
    if ((status & error_mask) != status_mask) {
        VPRINTF(LOW, "ERROR: unexpected status: expected: %08X actual: %08X\n", status_mask, status);
    }
    VPRINTF(LOW, "DEBUG: DAI is now idle.\n");
    return;
}

void initialize_otp_controller(void) {
    uint32_t status;

    // Step 1: Check OTP controller initialization status
    VPRINTF(LOW, "DEBUG: Checking OTP controller initialization status...\n");
    status = lsu_read_32(SOC_OTP_CTRL_STATUS);

    // Check for error bits in the status register
    if (status & 0x3FFFFF != 0 ) { // Mask all bits except DAI_IDLE
        VPRINTF(LOW, "ERROR: OTP controller initialization failed. STATUS: 0x%08X\n", status);
        return;
    }

    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: OTP controller successfully initialized. STATUS: 0x%08X\n", status);

    // Step 2: Set up periodic background checks
    VPRINTF(LOW, "DEBUG: Configuring periodic background checks...\n");
    
    // Configure CHECK_TIMEOUT
    uint32_t check_timeout = 0x100000; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_CHECK_TIMEOUT, check_timeout);
    VPRINTF(LOW, "INFO: CHECK_TIMEOUT set to 0x%08X\n", check_timeout);

    // Configure INTEGRITY_CHECK_PERIOD
    uint32_t integrity_check_period = 0x3FFFF; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_INTEGRITY_CHECK_PERIOD, integrity_check_period);
    VPRINTF(LOW, "INFO: INTEGRITY_CHECK_PERIOD set to 0x%08X\n", integrity_check_period);

    // Configure CONSISTENCY_CHECK_PERIOD
    uint32_t consistency_check_period = 0x3FFFF; // Example value, adjust as needed
    lsu_write_32(SOC_OTP_CTRL_CONSISTENCY_CHECK_PERIOD, consistency_check_period);
    VPRINTF(LOW, "INFO: CONSISTENCY_CHECK_PERIOD set to 0x%08X\n", consistency_check_period);

    // Step 3: Lock down background check registers
    VPRINTF(LOW, "DEBUG: Locking background check registers...\n");
    lsu_write_32(SOC_OTP_CTRL_CHECK_REGWEN, 0x0);
    VPRINTF(LOW, "INFO: CHECK_REGWEN locked.\n");
}

#define FUSE_CTRL_CMD_DAI_ZER 0x8
#define FUSE_CTRL_CMD_DAI_DIG 0x4
#define FUSE_CTRL_CMD_DAI_WRITE 0x2
#define FUSE_CTRL_CMD_DAI_READ  0x1

void dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1, uint32_t granularity, uint32_t exp_status) {
    VPRINTF(LOW, "DEBUG: Starting DAI write operation...\n");

    //wait_dai_op_idle(0);

    VPRINTF(LOW, "DEBUG: Writing wdata0: 0x%08X to DIRECT_ACCESS_WDATA_0.\n", wdata0);
    lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, wdata0);

    if (granularity == 64) {
        VPRINTF(LOW, "DEBUG: Writing wdata1: 0x%08X to DIRECT_ACCESS_WDATA_1.\n", wdata1);
        lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, wdata1);
    }

    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "DEBUG: Triggering DAI write command.\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_WRITE);

    wait_dai_op_idle(exp_status);
    return;
}

void dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1, uint32_t granularity, uint32_t exp_status) {
    VPRINTF(LOW, "DEBUG: Starting DAI read operation...\n");

    //wait_dai_op_idle(0);

    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "DEBUG: Triggering DAI read command.\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_READ);

    wait_dai_op_idle(exp_status);

    *rdata0 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
    VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", *rdata0);

    if (granularity == 64) {
        *rdata1 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
        VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", *rdata1);
    }
    return;
}

void calculate_digest(uint32_t partition_base_address, uint32_t exp_status) {
    // Step 1: Check if DAI is idle
    wait_dai_op_idle(0);

    // Step 2: Write the partition base address to DIRECT_ACCESS_ADDRESS
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, partition_base_address);
    VPRINTF(LOW, "INFO: Partition base address 0x%08X written to DIRECT_ACCESS_ADDRESS.\n", partition_base_address);

    // Step 3: Trigger a digest calculation command
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, 0x4);

    // Step 4: Poll STATUS until the DAI is idle and check that it matches the expected status
    wait_dai_op_idle(exp_status);
    return;
}

void dai_zer(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1, uint32_t granularity, uint32_t exp_status) {
    VPRINTF(LOW, "DEBUG: Starting DAI zeroization operation...\n");

    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "DEBUG: Triggering DAI Zeroize command.\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_ZER);

    wait_dai_op_idle(exp_status);

    *rdata0 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
    VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", *rdata0);

    if (granularity == 64) {
        *rdata1 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
        VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", *rdata1);
    }

    return;
}


void shuffled_dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1, uint32_t granularity, uint32_t exp_status, uint8_t permutation_index) {
    VPRINTF(LOW, "DEBUG: Starting DAI write operation with permutation %d...\n", permutation_index);

    switch (permutation_index) {
        case 0: // Original order
            lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, wdata0);
            if (granularity == 64)
                lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, wdata1);
            lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);
            break;

        case 1: // Swap wdata0 and wdata1
            if (granularity == 64)
                lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, wdata1);
            lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, wdata0);
            lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);
            break;

        case 2: // Address first
            lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);
            lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, wdata0);
            if (granularity == 64)
                lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, wdata1);
            break;

        case 3: // wdata0, address, wdata1
            lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, wdata0);
            lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);
            if (granularity == 64)
                lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, wdata1);
            break;

        case 4: // wdata1, address, wdata0
            if (granularity == 64)
                lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, wdata1);
            lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);
            lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, wdata0);
            break;

        default:
            VPRINTF(LOW, "ERROR: Invalid permutation index %d\n", permutation_index);
            return;
    }

    VPRINTF(LOW, "DEBUG: Triggering DAI write command.\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_WRITE);

    wait_dai_op_idle(exp_status);
}


void shuffled_dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1, uint32_t granularity, uint32_t exp_status, uint8_t permutation_index) {
    VPRINTF(LOW, "DEBUG: Starting DAI read operation with permutation %d...\n", permutation_index);

    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "DEBUG: Triggering DAI read command.\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_READ);

    wait_dai_op_idle(exp_status);

    switch (permutation_index) {
        case 0: // Read rdata0 first, then rdata1
            *rdata0 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
            VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", *rdata0);

            if (granularity == 64) {
                *rdata1 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
                VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", *rdata1);
            }
            break;

        case 1: // Read rdata1 first, then rdata0
            if (granularity == 64) {
                *rdata1 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
                VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", *rdata1);
            }

            *rdata0 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
            VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", *rdata0);
            break;

        default:
            VPRINTF(LOW, "WARNING: Unsupported permutation index %d. Defaulting to standard read order.\n", permutation_index);
            *rdata0 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0);
            VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", *rdata0);

            if (granularity == 64) {
                *rdata1 = lsu_read_32(SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1);
                VPRINTF(LOW, "DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", *rdata1);
            }
            break;
    }

    return;
}


void calculate_digest_without_addr(uint32_t exp_status) {
    // Step 1: Check if DAI is idle
    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: Triggering DIGEST WITHOUT ADDRESS.\n");

    // Step 3: Trigger a digest calculation command
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, 0x4);

    // Step 4: Poll STATUS until the DAI is idle and check that it matches the expected status
    wait_dai_op_idle(exp_status);
    return;
}


void zeroize_without_addr(uint32_t exp_status) {
    // Step 1: Check if DAI is idle
    wait_dai_op_idle(0);

    VPRINTF(LOW, "INFO: Triggering ZEROIZE WITHOUT ADDRESS.\n");

    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, FUSE_CTRL_CMD_DAI_ZER);

    wait_dai_op_idle(exp_status);
    return;
}

bool is_caliptra_secret_addr(uint32_t addr) {
    // This mirrors CALIPTRA_SECRET_ACCESS_LOWER_ADDR and CALIPTRA_SECRET_ACCESS_UPPER_ADDR in
    // otp_ctrl_pkg. Here, we're using the fact that the secret partitions are a contiguous block,
    // starting with SECRET_MANUF_PARTITION and ending with SECRET_PROD_PARTITION_3.
    return ((addr >= partitions[SECRET_MANUF_PARTITION].address) &&
            (addr <= partitions[SECRET_PROD_PARTITION_3].zer_address));
}
