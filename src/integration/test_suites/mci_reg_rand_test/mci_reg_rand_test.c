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

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    int total_reg_count;
    int error_count = 0;

    VPRINTF(LOW, "==================\nMCI Registers Test\n==================\n\n");

    mci_init();

    // Exclude registers from writing during group write
    exclude_register(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO);
    exclude_register(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    exclude_register(SOC_MBOX_CSR_MBOX_LOCK);
    exclude_register(SOC_MBOX_CSR_MBOX_USER);
    
    // Loop through all RW register groups
    for (mci_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
        if ((group == REG_GROUP_TRACE_RO) ||
            (group == REG_GROUP_TRACE) ||
            (group == REG_GROUP_SOC_MBOX_CSR)) {
            continue;
        } else if ((group == REG_GROUP_KNOWN_VALUES) ||
            (group == REG_GROUP_CAPABILITIES_RO) ||
            (group == REG_GROUP_STATUS_RO) ||
            (group == REG_GROUP_SECURITY_RO) ||
            (group == REG_GROUP_WATCHDOG_RO) ||
            (group == REG_GROUP_MCU_MBOX0_RO) ||
            (group == REG_GROUP_MCU_MBOX1_RO) ||
            (group == REG_GROUP_GENERIC_WIRES_RO) ||
            (group == REG_GROUP_SS_RO) ) {
            read_register_group_and_track(group, &g_expected_data_dict);
        }
        else {
            // Write random values to all registers in this group
            write_random_to_register_group_and_track(group, &g_expected_data_dict);    
        }    
    }

    // Loop through all register groups and verify
    for (mci_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
        if ((group == REG_GROUP_TRACE_RO) ||
            (group == REG_GROUP_TRACE) ||
            (group == REG_GROUP_SOC_MBOX_CSR)) {
            continue;
        } else {
            error_count += read_register_group_and_verify(group, &g_expected_data_dict);
        }
    }

    // Write 0x1 to CONFIG_DONE_STICKY and CONFIG_DONE registers
    write_to_register_group_and_track(REG_GROUP_SS, 0x1, &g_expected_data_dict); 

    read_register_group_and_verify(REG_GROUP_SS, &g_expected_data_dict); 

    // Write PK_HASH -- should fail
    write_to_register_group_and_track(REG_GROUP_DEBUG_UNLOCK_PK_HASH_3, 0x1, &g_expected_data_dict); 

    read_register_group_and_verify(REG_GROUP_DEBUG_UNLOCK_PK_HASH_3, &g_expected_data_dict); 


    VPRINTF(LOW, "Completed writing random values to all register groups.\n");
 
    total_reg_count = get_total_register_count();
    VPRINTF(MEDIUM, "TOtal Register Count: %d", total_reg_count);
 
    
    VPRINTF(LOW, "\nMCI Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(0xff);
    } else {
        SEND_STDOUT_CTRL(0x1);
    }
}