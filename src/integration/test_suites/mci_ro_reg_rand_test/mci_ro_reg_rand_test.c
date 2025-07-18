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

    VPRINTF(LOW, "==================\nMCI Registers Test\n==================\n\n");

    mci_register_group_t ro_reg_groups[] = {
        REG_GROUP_KNOWN_VALUES,
        REG_GROUP_CAPABILITIES_RO,
        REG_GROUP_STRAPS_RO,
        REG_GROUP_STATUS_RO,
        REG_GROUP_SECURITY_RO,
        REG_GROUP_WATCHDOG_RO,
        REG_GROUP_GENERIC_WIRES_RO,
        REG_GROUP_SS_RO
    };

    const int num_groups =  sizeof(ro_reg_groups) / sizeof(ro_reg_groups[0]);

    if (rst_count == 1) {

        mci_init();
    
        // Loop through all RO register groups
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = ro_reg_groups[i];

            // Read registers and record expected data
            read_register_group_and_track(group, &g_expected_data_dict);
            
            // Read registers and verify
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET);        
        }

        // Lock registers with SS_CONFIG_DONE_STICKY and SS_CONFIG_DONE registers by writing 0x1 to them
        write_to_register_group_and_track(REG_GROUP_SS, 0x1, &g_expected_data_dict);   

        read_register_group_and_verify(REG_GROUP_SS, &g_expected_data_dict, false, COLD_RESET); 

        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = ro_reg_groups[i];

            // Write random values and confirm write fails
            write_random_to_register_group_and_track(group, &g_expected_data_dict);

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET);
        }

        // Issue warm reset
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 2) {

        // Loop through all RO register groups
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = ro_reg_groups[i];

            // Read registers and record expected data
            read_register_group_and_track(group, &g_expected_data_dict);
                
            // Read registers and verify
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, WARM_RESET);       
        }
    
        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 3) {

        // Loop through all RO register groups
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = ro_reg_groups[i];

            // Read registers and record expected data
            read_register_group_and_track(group, &g_expected_data_dict);
            
            // Read registers and verify
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, COLD_RESET);       
        }
    }
    
    VPRINTF(LOW, "Read-Only register access tests completed.\n");
 
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
