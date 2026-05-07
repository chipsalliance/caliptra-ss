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
volatile int rst_cnt = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void write_random_to_register_group(mci_register_group_t group) {
    int count = get_register_count(group);
    VPRINTF(LOW, "Writing random values to all %s registers (%d total):\n", get_group_name(group), count);

    for (int i = 0; i < count; i++) {
        const mci_register_info_t *reg = get_register_info(group, i);

        if (reg) {
            // Check if this register should be excluded using our efficient method
            if (!is_register_excluded(reg->address)) {
                // Generate a unique value for each register
                uint32_t rand_value = xorshift32();

                /* Get mask for this register */
                uint32_t mask = get_register_mask(reg->address);

                VPRINTF(MEDIUM, "  Writing 0x%08x to %s (0x%08x)\n", rand_value, reg->name, reg->address);
                mci_reg_write(reg->address, rand_value);
            } else {
                VPRINTF(MEDIUM, "  Skipping excluded register %s (0x%08x)\n", reg->name, reg->address);
            }
        }
    }
}

void main(void) {

   if (rst_cnt == 1) {
        // SHould never reach this
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
   }

    VPRINTF(LOW, "==================\nMCI Registers Invalid AXI User Access Test\n==================\n\n");
    rst_cnt = 1;

    mci_register_group_t mci_reg_groups[] = {
        REG_GROUP_STATUS,
        REG_GROUP_INTERNAL_ERROR_MASK,
        REG_GROUP_WATCHDOG,
        REG_GROUP_MCU,
        REG_GROUP_INTERRUPT_EN,
        REG_GROUP_INTERRUPT_ERROR0_COUNTERS,
        REG_GROUP_INTERRUPT_ERROR1_COUNTERS,
        REG_GROUP_INTERRUPT_NOTIF0_COUNTERS,
        REG_GROUP_INTERRUPT_NOTIF1_COUNTERS
    };

    const int num_groups =  sizeof(mci_reg_groups) / sizeof(mci_reg_groups[0]);

    mci_init();

    // Exclude registers from writing during group write
    exclude_register(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO);
    exclude_register(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    exclude_register(SOC_MCI_TOP_MCI_REG_MCU_TIMER_CONFIG);
    exclude_register(SOC_MCI_TOP_MCI_REG_WDT_CFG_0);
    exclude_register(SOC_MCI_TOP_MCI_REG_WDT_CFG_1);

    // Loop through all RW register groups
    for (int i = 0; i < num_groups; i++) {
        mci_register_group_t group = mci_reg_groups[i];

        // Write random values to all registers in this group
        write_random_to_register_group_and_track(group, &g_expected_data_dict);

        // Change AXI USER and try acessing locked registers
        SEND_STDOUT_CTRL(TB_CHANGE_STRAP_MCU_LSU_AXI_USER);
        write_random_to_register_group(group);
        SEND_STDOUT_CTRL(TB_RELEASE_STRAP_MCU_LSU_AXI_USER);

        // Read registers and verify data matches
        error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET);
    }

    // Clear notif 0 register
    lsu_write_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, lsu_read_32(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R));
    // Change AXI USER and try triggering interrupts
    SEND_STDOUT_CTRL(TB_CHANGE_STRAP_MCU_LSU_AXI_USER);
    write_random_to_register_group(REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S);
    SEND_STDOUT_CTRL(TB_RELEASE_STRAP_MCU_LSU_AXI_USER);

    // Check that no interrupts were raised
    error_count += read_register_group_and_verify(REG_GROUP_INTERRUPT_STATUS_RW1C, &g_expected_data_dict, false, COLD_RESET);

    // Raise some random interrupts
    write_random_to_register_group_and_track(REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S, &g_expected_data_dict);

    // Change AXI USER and try clearing interrupts
    SEND_STDOUT_CTRL(TB_CHANGE_STRAP_MCU_LSU_AXI_USER);
    write_random_to_register_group(REG_GROUP_INTERRUPT_STATUS_RW1C);
    SEND_STDOUT_CTRL(TB_RELEASE_STRAP_MCU_LSU_AXI_USER);

    // Check that interrupts were not cleared
    error_count += read_register_group_and_verify(REG_GROUP_INTERRUPT_STATUS_RW1C, &g_expected_data_dict, false, COLD_RESET);

    // Change AXI USER and try requesting reset
    SEND_STDOUT_CTRL(TB_CHANGE_STRAP_MCU_LSU_AXI_USER);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_RESET_REQUEST, 0x1);
    SEND_STDOUT_CTRL(TB_RELEASE_STRAP_MCU_LSU_AXI_USER);

    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REQUEST) == 0x1) {
        VPRINTF(LOW, "RESET_REQUEST incorrectly accessed\n");
        error_count += 1;
    }

    VPRINTF(LOW, "\nMCI Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
