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
#include "fuse_ctrl_address_map.h"
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

    VPRINTF(LOW, "==========================\nMCI Error & Interrupt Registers Test\n===========================\n\n");

    mci_register_group_t err_intr_groups[] = {
        //REG_GROUP_ERROR_RW1C,
        //REG_GROUP_ERROR,
        REG_GROUP_INTERNAL_ERROR_MASK,
        //REG_GROUP_INTERRUPT_EN,
        REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO,
        REG_GROUP_INTERRUPT_STATUS_RW1C,
        REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S,
        REG_GROUP_INTERRUPT_ERROR0_COUNTERS,
        REG_GROUP_INTERRUPT_NOTIF0_COUNTERS
    };

    const int num_groups = sizeof(err_intr_groups) / sizeof(err_intr_groups[0]);

    // Loop through all PK Hash register groups and write/read random values to registers
    if (rst_count == 1) {

        mci_init();

        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = err_intr_groups[i];
                
            // Write random values to all PK Hash registers
            if (group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO){
                continue;
            } else {
                write_random_to_register_group_and_track(group, &g_expected_data_dict);
            }
                
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET);
        }

        // Lock registers with SS_CONFIG_DONE_STICKY and SS_CONFIG_DONE registers by writing 0x1 to them
        write_to_register_group_and_track(REG_GROUP_SS, 0x1, &g_expected_data_dict); 

        read_register_group_and_verify(REG_GROUP_SS, &g_expected_data_dict, false, COLD_RESET); 

        // Loop through register groups and write/read random values
        // Registers that are sticky, new value should not be written
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = err_intr_groups[i];
                
            // Write random values to all interrupt registers
            if (group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO){
                continue;
            } else {
                write_random_to_register_group_and_track(group, &g_expected_data_dict);
            }
                
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET);

        }

        // Issue warm reset
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 2) {

        // Read all registers, expect register values to be retained for sticky registers
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = err_intr_groups[i];
                
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, WARM_RESET);

            // Write random values to all interrupt registers
            if (group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO){
                continue;
            } else {
                write_random_to_register_group_and_track(group, &g_expected_data_dict);
            }
                
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, WARM_RESET);
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 3) {

        // Read all registers, expect register values to be reset
        for (int i = 0; i < num_groups; i++) {
            mci_register_group_t group = err_intr_groups[i];
                
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, COLD_RESET);

        }
    }
 
    VPRINTF(LOW, "\nMCI Error and Interrupt Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(0xff);
    } else {
        SEND_STDOUT_CTRL(0x1);
    }
}
