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

#include "mci.h"
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "veer-csr.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
volatile int error_count = 0;
volatile int rst_count  = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    
    rst_count++;
    VPRINTF(LOW, "----------------\nrst count = %d\n----------------\n", rst_count);

    VPRINTF(LOW, "=========================\nMCI Debug Hash Registers Test\n=========================\n\n");

    mci_register_group_t pk_hash_groups[] = {
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_0,
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_1,
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_2,
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_3,
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_4,
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_5,
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_6,
        REG_GROUP_DEBUG_UNLOCK_PK_HASH_7
    };

    const int num_groups = sizeof(pk_hash_groups) / sizeof(pk_hash_groups[0]);

    // Loop through all PK Hash register groups and write/read random values to registers
    if (rst_count == 1) {

        mci_init();

        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = pk_hash_groups[i];
            
            // Write random values to all PK Hash registers
            write_random_to_register_group_and_track(group, &g_expected_data_dict);
                
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET);
            
        }

        // Lock registers with SS_CONFIG_DONE_STICKY and SS_CONFIG_DONE registers by writing 0x1 to them
        write_to_register_group_and_track(REG_GROUP_SS, 0x1, &g_expected_data_dict); 

        read_register_group_and_verify(REG_GROUP_SS, &g_expected_data_dict, false, COLD_RESET); 

        // Loop through all PK Hash register groups and write/read random values
        // Registers are sticky, new value should not be written
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = pk_hash_groups[i];
                
            // Write random values to all PK Hash registers
            write_random_to_register_group_and_track(group, &g_expected_data_dict);
                
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET);
        }

        // Issue warm reset
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 2) {

        // Read all registers, expect register values to be retained
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = pk_hash_groups[i];

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, WARM_RESET);
                
            // Write random values to all PK Hash registers
            write_random_to_register_group_and_track(group, &g_expected_data_dict);
                
            // Read registers and verify data matches original writes
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, WARM_RESET);
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 3) {

        // Read all registers, expect register values to be reset
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = pk_hash_groups[i];

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, COLD_RESET);
        }

    }
 
    VPRINTF(LOW, "\nMCI PK Hash Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
