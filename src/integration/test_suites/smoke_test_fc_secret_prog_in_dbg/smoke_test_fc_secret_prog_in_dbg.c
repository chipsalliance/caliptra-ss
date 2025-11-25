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

/**
 * Attempt to program `UDS` while caliptra is in debug mode, this prov should fail
 * 
 *   1. Write a value to a first UDS address, one of any FE0 address and
 *      the end of FE3 address.
 *   2. Read back the value and verify it is equal to the value written in Step 1.
 *   3. If yes, fail the test.
 *   4. Otherwise, pass the test.
 */
void program_UDS_FE_secret_prod_partition() {
    // Set AXI user ID to 1.
    VPRINTF(LOW, "INFO: Granting MCU access to fuse controller...\n");
    grant_caliptra_core_for_fc_writes();


    partition_t hw_part_uds = partitions[SECRET_MANUF_PARTITION];
    partition_t hw_part_fe0 = partitions[SECRET_PROD_PARTITION_0];
    partition_t hw_part_fe3 = partitions[SECRET_PROD_PARTITION_3];

    uint32_t uds_base_address = hw_part_uds.address;
    uint32_t fe0_base_address = hw_part_fe0.address;
    uint32_t fe3_last_address = hw_part_fe3.address;

    uint32_t data[2] = { 0xA5A5A5A5, 0x5A5A5A5A };
    uint32_t uds_read_data[2];
    uint32_t fe0_read_data[2];
    uint32_t fe3_read_data[2];
    uint32_t read_data[2];
    dai_rd(uds_base_address, &uds_read_data[0], &uds_read_data[1], 64, 0);
    dai_rd(fe0_base_address, &fe0_read_data[0], &fe0_read_data[1], 64, 0);
    dai_rd(fe3_last_address, &fe3_read_data[0], &fe3_read_data[1], 64, 0);

    // Step 1
    dai_wr(uds_base_address, data[0], data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(fe0_base_address, data[0], data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);
    dai_wr(fe3_last_address, data[0], data[1], 64, OTP_CTRL_STATUS_DAI_ERROR_MASK);

    // Step 2, 3, 4
    dai_rd(uds_base_address, &read_data[0], &read_data[1], 64, 0);
    if (uds_read_data[0]!= read_data[0] || uds_read_data[1] != read_data[1]) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", uds_read_data[0], read_data[0]);
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", uds_read_data[1], read_data[1]);
        handle_error("Data mismatch detected when reading UDS fuse in debug mode");
    }
    dai_rd(fe0_base_address, &read_data[0], &read_data[1], 64, 0);
    if (fe0_read_data[0]!= read_data[0] || fe0_read_data[1] != read_data[1]) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", fe0_read_data[0], read_data[0]);
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", fe0_read_data[1], read_data[1]);
        handle_error("Data mismatch detected when reading FE0 fuse in debug mode");
    }
    dai_rd(fe3_last_address, &read_data[0], &read_data[1], 64, 0);
    if (fe3_read_data[0]!= read_data[0] || fe3_read_data[1] != read_data[1]) {
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", fe3_read_data[0], read_data[0]);
        VPRINTF(LOW, "ERROR: incorrect fuse data: expected: %08X actual: %08X\n", fe3_read_data[1], read_data[1]);
        handle_error("Data mismatch detected when reading FE3 fuse in debug mode");
    }


    VPRINTF(LOW, "DEBUG: UDS/FE programming rules are applied successfully\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");
    
    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    
    lcc_initialization();

    uint32_t lc_state_curr = read_lc_state();
    if (lc_state_curr != 1) {
        handle_error("ERROR: LCC is not initialized from TEST_UNLOCKED0\n");
    }

    program_UDS_FE_secret_prod_partition();

    mcu_sleep(160);


    SEND_STDOUT_CTRL(0xff);
}