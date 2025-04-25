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


    VPRINTF(LOW, "==================\nMCI Registers Test\n==================\n\n");

    if (rst_count == 1) {

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
                (group == REG_GROUP_SOC_MBOX_CSR) ||
                (group == REG_GROUP_SS)|| 
                (group == REG_GROUP_MCU_MBOX0_RO) ||
                (group == REG_GROUP_MCU_MBOX0) ||
                (group == REG_GROUP_MCU_MBOX1_RO) ||
                (group == REG_GROUP_MCU_MBOX1) ||
                (group == REG_GROUP_KNOWN_VALUES) ||
                (group == REG_GROUP_CAPABILITIES_RO) ||
                (group == REG_GROUP_STATUS_RO) ||
                (group == REG_GROUP_SECURITY_RO) ||
                (group == REG_GROUP_WATCHDOG_RO) ||
                (group == REG_GROUP_GENERIC_WIRES_RO) ||
                (group == REG_GROUP_SS_RO) ||
                (group == REG_GROUP_ERROR_W1C) ||
                (group == REG_GROUP_ERROR) ||
                (group == REG_GROUP_INTERRUPT) ||
                (group == REG_GROUP_INTERRUPT_COUNTERS) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_0) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_1) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_2) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_3) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_4) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_5) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_6) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_7)) { // Config done and config done sticky registers will be written after all reg writes are complete
                continue;
            } else {
                // Write random values to all registers in this group
                write_random_to_register_group_and_track(group, &g_expected_data_dict);  
                
                // Read registers and verify data matches
                error_count += read_register_group_and_verify(group, &g_expected_data_dict);
            }    
        }

        // Lock registers with SS_CONFIG_DONE_STICKY and SS_CONFIG_DONE registers by writing 0x1 to them
        write_to_register_group_and_track(REG_GROUP_SS, 0x1, &g_expected_data_dict); 

        read_register_group_and_verify(REG_GROUP_SS, &g_expected_data_dict); 

        // Loop through all RW register groups -- sticky registers should not be updated
        for (mci_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
            if ((group == REG_GROUP_TRACE_RO) ||
                (group == REG_GROUP_TRACE) ||
                (group == REG_GROUP_SOC_MBOX_CSR) ||
                (group == REG_GROUP_SS)|| 
                (group == REG_GROUP_MCU_MBOX0_RO) ||
                (group == REG_GROUP_MCU_MBOX0) ||
                (group == REG_GROUP_MCU_MBOX1_RO) ||
                (group == REG_GROUP_MCU_MBOX1) ||
                (group == REG_GROUP_KNOWN_VALUES) ||
                (group == REG_GROUP_CAPABILITIES_RO) ||
                (group == REG_GROUP_STATUS_RO) ||
                (group == REG_GROUP_SECURITY_RO) ||
                (group == REG_GROUP_WATCHDOG_RO) ||
                (group == REG_GROUP_GENERIC_WIRES_RO) ||
                (group == REG_GROUP_SS_RO) ||
                (group == REG_GROUP_ERROR) ||
                (group == REG_GROUP_ERROR_W1C) ||
                (group == REG_GROUP_INTERRUPT) ||
                (group == REG_GROUP_INTERRUPT_COUNTERS) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_0) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_1) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_2) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_3) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_4) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_5) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_6) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_7)) { // Config done and config done sticky registers will be written after all reg writes are complete
                continue;
            } else {
                // Write random values to all registers in this group
                write_random_to_register_group_and_track(group, &g_expected_data_dict);  
                
                // Read registers and verify data matches
                error_count += read_register_group_and_verify(group, &g_expected_data_dict);
            }    
        }

        // Issue warm reset
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 2) {

        reset_exp_reg_data(&g_expected_data_dict, WARM_RESET);

        // Read all registers, expect register values to be retained fr sticky registers
        for (mci_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
            if ((group == REG_GROUP_TRACE_RO) ||
                (group == REG_GROUP_TRACE) ||
                (group == REG_GROUP_SOC_MBOX_CSR) ||
                (group == REG_GROUP_SS)|| 
                (group == REG_GROUP_MCU_MBOX0_RO) ||
                (group == REG_GROUP_MCU_MBOX0) ||
                (group == REG_GROUP_MCU_MBOX1_RO) ||
                (group == REG_GROUP_MCU_MBOX1) ||
                (group == REG_GROUP_KNOWN_VALUES) ||
                (group == REG_GROUP_CAPABILITIES_RO) ||
                (group == REG_GROUP_STATUS_RO) ||
                (group == REG_GROUP_SECURITY_RO) ||
                (group == REG_GROUP_WATCHDOG_RO) ||
                (group == REG_GROUP_GENERIC_WIRES_RO) ||
                (group == REG_GROUP_SS_RO) ||
                (group == REG_GROUP_ERROR) ||
                (group == REG_GROUP_ERROR_W1C) ||
                (group == REG_GROUP_INTERRUPT) ||
                (group == REG_GROUP_INTERRUPT_COUNTERS) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_0) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_1) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_2) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_3) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_4) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_5) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_6) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_7)) { // Config done and config done sticky registers will be written after all reg writes are complete
                continue;
            } else {
                // Read registers and verify data matches
                error_count += read_register_group_and_verify(group, &g_expected_data_dict);
            }    
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);

        // Halt the MCU
        csr_write_mpmc_halt();

    } else if (rst_count == 3) {

        reset_exp_reg_data(&g_expected_data_dict, COLD_RESET);

        // Read all registers, expect register values to be reset
        for (mci_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
            if ((group == REG_GROUP_TRACE_RO) ||
                (group == REG_GROUP_TRACE) ||
                (group == REG_GROUP_SOC_MBOX_CSR) ||
                (group == REG_GROUP_SS)|| 
                (group == REG_GROUP_MCU_MBOX0_RO) ||
                (group == REG_GROUP_MCU_MBOX0) ||
                (group == REG_GROUP_MCU_MBOX1_RO) ||
                (group == REG_GROUP_MCU_MBOX1) ||
                (group == REG_GROUP_KNOWN_VALUES) ||
                (group == REG_GROUP_CAPABILITIES_RO) ||
                (group == REG_GROUP_STATUS_RO) ||
                (group == REG_GROUP_SECURITY_RO) ||
                (group == REG_GROUP_WATCHDOG_RO) ||
                (group == REG_GROUP_GENERIC_WIRES_RO) ||
                (group == REG_GROUP_SS_RO) ||
                (group == REG_GROUP_ERROR) ||
                (group == REG_GROUP_ERROR_W1C) ||
                (group == REG_GROUP_INTERRUPT) ||
                (group == REG_GROUP_INTERRUPT_COUNTERS) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_0) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_1) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_2) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_3) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_4) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_5) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_6) ||
                (group == REG_GROUP_DEBUG_UNLOCK_PK_HASH_7)) { // Config done and config done sticky registers will be written after all reg writes are complete
                continue;
            } else {
                // Read registers and verify data matches
                error_count += read_register_group_and_verify(group, &g_expected_data_dict);
            }    
        }
    }

    VPRINTF(LOW, "\nMCI (excluding error, interrupt and PK Hash registers) Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
