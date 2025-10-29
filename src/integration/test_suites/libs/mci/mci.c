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
#include "string.h"
#include "stdint.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "caliptra_ss_lib.h"

#define ADDRESS_BITS_FOR_INDEXING 12   // 4096 possible indices
#define BITMAP_SIZE_WORDS ((1 << ADDRESS_BITS_FOR_INDEXING) / 32)

uint32_t get_mcu_sram_size(){
    return (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_CONFIG1)  & MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_MASK) >> MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_LOW;
}

uint32_t get_mcu_sram_size_byte(){
    return get_mcu_sram_size() * 1024;
}

uint32_t get_mcu_sram_end_addr(){
   return SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + get_mcu_sram_size_byte() - 1;

}

uint32_t get_mcu_sram_last_dword(){
    return get_mcu_sram_end_addr() & ~3;
}

uint32_t get_mcu_sram_execution_region_start() {
    return SOC_MCI_TOP_MCU_SRAM_BASE_ADDR;
}

uint32_t get_mcu_sram_execution_region_end() {
    uint32_t fw_exec_region;

    fw_exec_region = lsu_read_32(SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE) + 1; // BASE 0 so add 1 for any calculations
    
    return get_mcu_sram_execution_region_start() + (fw_exec_region * 4 * 1024) -1;

}

uint32_t get_fw_sram_exec_region_less_than_sram_size(uint32_t rnd){
    uint32_t mask_rnd = rnd & MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK;
    uint32_t sram_size = get_mcu_sram_size();
    uint32_t fw_sram_exec_region = (mask_rnd % sram_size) >> 4;
    return fw_sram_exec_region;
}

bool get_is_sram_protected_region(){
    return get_mcu_sram_protected_region_start() <= get_mcu_sram_end_addr();
}

uint32_t get_mcu_sram_protected_region_start() {
    return get_mcu_sram_execution_region_end() + 1;
}

uint32_t get_mcu_sram_protected_region_end() {
   return get_mcu_sram_end_addr();

}

// The bitmap array for register exclusions
uint32_t excluded_registers_bitmap[BITMAP_SIZE_WORDS];

// Collision table to handle hash collisions - stores full register addresses
#define MAX_EXCLUDED_REGISTERS 32
static uint32_t collision_table[MAX_EXCLUDED_REGISTERS] = {0};
static uint8_t collision_count = 0;

/* Global dictionary for expected register values */
mci_reg_exp_dict_t g_expected_data_dict;
static register_mask_dict_t g_mask_dict;

/**
 * Read a 32-bit MCI register value
 * 
 * @param reg_addr Register address
 * @return The register value
 */
uint32_t mci_reg_read(uint32_t reg_addr) {
    return lsu_read_32(reg_addr);
}

/**
 * Write a 32-bit value to an MCI register
 * 
 * @param reg_addr Register address
 * @param value Value to write
 */
void mci_reg_write(uint32_t reg_addr, uint32_t value) {
    lsu_write_32(reg_addr, value);
}

// Array of register with non-zero initial values
const mci_reg_def_value_t reg_init_values[] = {
    {SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_1, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_2, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_3, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_0, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_1, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_2, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_3, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_4, 0xFFFFFFFF},
    {SOC_MCI_TOP_MCI_REG_MCU_RESET_VECTOR, 0x80000000},
    {SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK, 0x3FFFF000}
};

/* Array of register infos by group */
const mci_register_info_t register_groups[][MAX_REGISTERS_PER_GROUP] = {
    // REG_GROUP_KNOWN_VALUES
    {
        { SOC_MCI_TOP_MCI_REG_HW_REV_ID, "HW_REV_ID", "Hardware Revision ID", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

  
    // REG_GROUP_CAPABILITIES
    {
        { SOC_MCI_TOP_MCI_REG_HW_CAPABILITIES, "HW_CAPABILITIES", "Hardware Capabilities", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_CAPABILITIES, "FW_CAPABILITIES", "Firmware Capabilities", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_CAP_LOCK, "CAP_LOCK", "Capability Lock", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_REV_ID_0, "FW_REV_ID_0", "Firmware Revision ID 0", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_REV_ID_1, "FW_REV_ID_1", "Firmware Revision ID 1", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker  
    },

    // REG_GROUP_CAPABILITIES_RO
    {
        { SOC_MCI_TOP_MCI_REG_HW_CONFIG0, "HW_CONFIG0", "Hardware Configuration 0", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_HW_CONFIG1, "HW_CONFIG1", "Hardware Configuration 1", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_STRAPS_RO
    {
        { SOC_MCI_TOP_MCI_REG_MCU_IFU_AXI_USER, "MCU_IFU_AXI_USER", "MCU IFU AXI User", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCU_LSU_AXI_USER, "MCU_LSU_AXI_USER", "MCU LSU AXI User", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCU_SRAM_CONFIG_AXI_USER, "MCU_SRAM_CONFIG_AXI_USER", "MCU SRAM Config AXI User", REG_NOT_STICKY, false} ,
        { SOC_MCI_TOP_MCI_REG_MCI_SOC_CONFIG_AXI_USER, "MCI_SOC_CONFIG_AXI_USER", "MCI SOC Config AXI User", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
    
    // REG_GROUP_STATUS
    {
        { SOC_MCI_TOP_MCI_REG_FW_FLOW_STATUS, "FW_FLOW_STATUS", "Firmware Flow Status", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_RESET_REASON, "RESET_REASON", "Reset Reason", REG_STICKY, false }, // bit 1 & 0 are not sticky
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_STATUS_RO
    {
        { SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS, "HW_FLOW_STATUS", "Hardware Flow Status", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_RESET_STATUS, "RESET_STATUS", "Reset Status", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_SECURITY_RO
    {
        { SOC_MCI_TOP_MCI_REG_SECURITY_STATE, "SECURITY_STATE", "Security State", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_ERROR_RW1C
    {
        { SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", "Hardware Ftl Err", REG_STICKY},
        { SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL, "AGG_ERROR_FATAL", "Aggregated Ftl Err", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL, "HW_ERROR_NON_FATAL", "Hardware Non-Ftl Err", REG_STICKY  },
        { SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL, "AGG_ERROR_NON_FATAL", "Aggregated Non-Ftl Err", REG_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
    
    // REG_GROUP_ERROR
    {
        { SOC_MCI_TOP_MCI_REG_FW_ERROR_FATAL, "FW_ERROR_FATAL", "Firmware Ftl Err", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_ERROR_NON_FATAL, "FW_ERROR_NON_FATAL", "Firmware Non-Ftl Err", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_HW_ERROR_ENC, "HW_ERROR_ENC", "Hardware Err Enc", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_ERROR_ENC, "FW_ERROR_ENC", "Firmware Err Enc", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_0, "FW_EXTENDED_ERROR_INFO_0", "Firmware Extended ErrInfo 0", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_1, "FW_EXTENDED_ERROR_INFO_1", "Firmware Extended ErrInfo 1", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_2, "FW_EXTENDED_ERROR_INFO_2", "Firmware Extended ErrInfo 2", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_3, "FW_EXTENDED_ERROR_INFO_3", "Firmware Extended ErrInfo 3", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_4, "FW_EXTENDED_ERROR_INFO_4", "Firmware Extended ErrInfo 4", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_5, "FW_EXTENDED_ERROR_INFO_5", "Firmware Extended ErrInfo 5", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_6, "FW_EXTENDED_ERROR_INFO_6", "Firmware Extended ErrInfo 6", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_7, "FW_EXTENDED_ERROR_INFO_7", "Firmware Extended ErrInfo 7", REG_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
    
    // REG_GROUP_INTERNAL_ERROR_MASK
    {
        { SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK, "INTERNAL_HW_ERROR_FATAL_MASK", "Internal Hardware ErrFtl Mask", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK, "INTERNAL_HW_ERROR_NON_FATAL_MASK", "Internal Hardware ErrNon-Ftl Mask", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK, "INTERNAL_AGG_ERROR_FATAL_MASK", "Internal Agg ErrFtl Mask", REG_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK, "INTERNAL_AGG_ERROR_NON_FATAL_MASK", "Internal Agg ErrNon-Ftl Mask", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK, "INTERNAL_FW_ERROR_FATAL_MASK", "Internal Firmware ErrFtl Mask", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK, "INTERNAL_FW_ERROR_NON_FATAL_MASK", "Internal Firmware ErrNon-Ftl Mask", REG_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
    
    // REG_GROUP_WATCHDOG
    {
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_EN, "WDT_TIMER1_EN", "Watchdog Timer 1 Enable", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_CTRL, "WDT_TIMER1_CTRL", "Watchdog Timer 1 Control", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0, "WDT_TIMER1_TIMEOUT_PERIOD_0", "Watchdog Timer 1 Timeout Period 0", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1, "WDT_TIMER1_TIMEOUT_PERIOD_1", "Watchdog Timer 1 Timeout Period 1", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN, "WDT_TIMER2_EN", "Watchdog Timer 2 Enable", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_CTRL, "WDT_TIMER2_CTRL", "Watchdog Timer 2 Control", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0, "WDT_TIMER2_TIMEOUT_PERIOD_0", "Watchdog Timer 2 Timeout Period 0", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1, "WDT_TIMER2_TIMEOUT_PERIOD_1", "Watchdog Timer 2 Timeout Period 1", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_WDT_CFG_0, "WDT_CFG_0", "Watchdog Timer 0 Config", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_WDT_CFG_1, "WDT_CFG_1", "Watchdog Timer 1 Config", REG_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_WATCHDOG_RO
    {
        { SOC_MCI_TOP_MCI_REG_WDT_STATUS, "WDT_STATUS", "Watchdog Status", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_MCU
    {
        { SOC_MCI_TOP_MCI_REG_MCU_TIMER_CONFIG, "MCU_TIMER_CONFIG", "MCU Timer Config", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L, "MCU_RV_MTIME_L", "MCU RiscV MTime Low", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H, "MCU_RV_MTIME_H", "MCU RiscV MTime High", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_L, "MCU_RV_MTIMECMP_L", "MCU RiscV MTimeCmp Low", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_H, "MCU_RV_MTIMECMP_H", "MCU RiscV MTimeCmp High", REG_STICKY, false }, 
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_CONTROL
    {
        { SOC_MCI_TOP_MCI_REG_RESET_REQUEST, "RESET_REQUEST", "Reset Request", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO, "MCI_BOOTFSM_GO", "MCI BootFSM Go", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, "CPTRA_BOOT_GO", "Caliptra Boot Go", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    }, 

    // REG_GROUP_CONTROL_RO (RW Tap Access in Debug mode)
    {
        { SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE, "FW_SRAM_EXEC_REGION_SIZE", "Firmware SRAM Execution Size", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, "MCU_NMI_VECTOR", "MCI Non Maskable Interrupt Vector", REG_NOT_STICKY, false }, 
        { SOC_MCI_TOP_MCI_REG_MCU_RESET_VECTOR, "MCU_RESET_VECTOR", "MCI Reset Vector", REG_NOT_STICKY, true }, 
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
    
    // REG_GROUP_MCI_MBOX0
    {
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0, "MBOX0_VALID_AXI_USER_0", "Mailbox 0 Valid AXI User 0", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_1, "MBOX0_VALID_AXI_USER_1", "Mailbox 0 Valid AXI User 1", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_2, "MBOX0_VALID_AXI_USER_2", "Mailbox 0 Valid AXI User 2", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_3, "MBOX0_VALID_AXI_USER_3", "Mailbox 0 Valid AXI User 3", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4, "MBOX0_VALID_AXI_USER_4", "Mailbox 0 Valid AXI User 4", REG_NOT_STICKY, true },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    }, 

    // REG_GROUP_MCI_MBOX0_RW1S
    {
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0, "MBOX0_AXI_USER_LOCK_0", "Mailbox 0 Valid AXI Lock 0", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_1, "MBOX0_AXI_USER_LOCK_1", "Mailbox 0 Valid AXI Lock 1", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_2, "MBOX0_AXI_USER_LOCK_2", "Mailbox 0 Valid AXI Lock 2", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_3, "MBOX0_AXI_USER_LOCK_3", "Mailbox 0 Valid AXI Lock 3", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4, "MBOX0_AXI_USER_LOCK_4", "Mailbox 0 Valid AXI Lock 4", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_MCU_MBOX0
    {
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER, "MBOX0_TARGET_USER", "Mailbox 0 Target User", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID, "MBOX0_TARGET_USER_VALID", "Mailbox 0 Target User Valid", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD, "MBOX0_CMD", "Mailbox 0 Command", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, "MBOX0_DLEN", "Mailbox 0 Data Length", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, "MBOX0_EXECUTE", "Mailbox 0 Execute", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS, "MBOX0_TARGET_STATUS", "Mailbox 0 Target Status", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS, "MBOX0_CMD_STATUS", "Mailbox 0 Command Status", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_MCU_MBOX0_RO
    {
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK, "MBOX0_LOCK", "Mailbox 0 Lock", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER, "MBOX0_USER", "Mailbox 0 User", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS, "MBOX0_HW_STATUS", "Mailbox 0 Hardware Status", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
    
    // REG_GROUP_MCI_MBOX1
    {
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_0, "MBOX1_VALID_AXI_USER_0", "Mailbox 1 Valid AXI User 0", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_1, "MBOX1_VALID_AXI_USER_1", "Mailbox 1 Valid AXI User 1", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_2, "MBOX1_VALID_AXI_USER_2", "Mailbox 1 Valid AXI User 2", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_3, "MBOX1_VALID_AXI_USER_3", "Mailbox 1 Valid AXI User 3", REG_NOT_STICKY, true },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_4, "MBOX1_VALID_AXI_USER_4", "Mailbox 1 Valid AXI User 4", REG_NOT_STICKY, true },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_MCI_MBOX1_RW1S
    {
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_0, "MBOX1_AXI_USER_LOCK_0", "Mailbox 1 Valid AXI Lock 0", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_1, "MBOX1_AXI_USER_LOCK_1", "Mailbox 1 Valid AXI Lock 1", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_2, "MBOX1_AXI_USER_LOCK_2", "Mailbox 1 Valid AXI Lock 2", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_3, "MBOX1_AXI_USER_LOCK_3", "Mailbox 1 Valid AXI Lock 3", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_4, "MBOX1_AXI_USER_LOCK_4", "Mailbox 1 Valid AXI Lock 4", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_MCU_MBOX1
    {
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_USER, "MBOX1_TARGET_USER", "Mailbox 1 Target User", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID, "MBOX1_TARGET_USER_VALID", "Mailbox 1 Target User Valid", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD, "MBOX1_CMD", "Mailbox 1 Command", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_DLEN, "MBOX1_DLEN", "Mailbox 1 Data Length", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_EXECUTE, "MBOX1_EXECUTE", "Mailbox 1 Execute", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_STATUS, "MBOX1_TARGET_STATUS", "Mailbox 1 Target Status", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD_STATUS, "MBOX1_CMD_STATUS", "Mailbox 1 Command Status", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_MCU_MBOX1_RO
    {
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_LOCK, "MBOX1_LOCK", "Mailbox 1 Lock", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_USER, "MBOX1_USER", "Mailbox 1 User", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_HW_STATUS, "MBOX1_HW_STATUS", "Mailbox 1 Hardware Status", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DFT
    {
        { SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_0, "SOC_DFT_EN_0", "SoC DFT Enable 0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_1, "SOC_DFT_EN_1", "SoC DFT Enable 1", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DEBUG
    {
        { SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_0, "HW_DEBUG_EN_0", "Hardware Debug Enable 0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_1, "HW_DEBUG_EN_1", "Hardware Debug Enable 1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_SOC_PROD_DEBUG_STATE_0, "PROD_DEBUG_STATE_0", "Production Debug State 0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_SOC_PROD_DEBUG_STATE_1, "PROD_DEBUG_STATE_1", "Production Debug State 1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_FC_FIPS_ZEROZATION, "FC_FIPS_ZEROZATION", "Fuse Controller FIPS Zeroization", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL , REG_NOT_STICKY}  // End marker
    },

    // REG_GROUP_GENERIC_WIRES
    { 
        { SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0, "GENERIC_OUTPUT_WIRES_0", "Generic Output Wires 0", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1, "GENERIC_OUTPUT_WIRES_1", "Generic Output Wires 1", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_GENERIC_WIRES_RO
    { 
        { SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0, "GENERIC_INPUT_WIRES_0", "Generic Input Wires 0", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1, "GENERIC_INPUT_WIRES_1", "Generic Input Wires 1", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_SS
    { 
        { SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE_STICKY, "SS_DCONFIG_DONE_STICKY", "Subsystem Config done sticky", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE, "SS_CONFIG_DONE", "Subsystem Config Done", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_SS_RO
    { 
        { SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT, "SS_DEBUG_INTENT", "Subsystem Debug Intent", REG_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
    
    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_0
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0", "Debug Unlock PK Hash 0_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1", "Debug Unlock PK Hash 0_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2", "Debug Unlock PK Hash 0_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3", "Debug Unlock PK Hash 0_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4", "Debug Unlock PK Hash 0_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5", "Debug Unlock PK Hash 0_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6", "Debug Unlock PK Hash 0_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7", "Debug Unlock PK Hash 0_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8", "Debug Unlock PK Hash 0_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9", "Debug Unlock PK Hash 0_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10", "Debug Unlock PK Hash 0_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11", "Debug Unlock PK Hash 0_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_1
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0", "Debug Unlock PK Hash 1_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1", "Debug Unlock PK Hash 1_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2", "Debug Unlock PK Hash 1_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3", "Debug Unlock PK Hash 1_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4", "Debug Unlock PK Hash 1_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5", "Debug Unlock PK Hash 1_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6", "Debug Unlock PK Hash 1_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7", "Debug Unlock PK Hash 1_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8", "Debug Unlock PK Hash 1_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9", "Debug Unlock PK Hash 1_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10", "Debug Unlock PK Hash 1_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11", "Debug Unlock PK Hash 1_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_2
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0", "Debug Unlock PK Hash 2_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1", "Debug Unlock PK Hash 2_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2", "Debug Unlock PK Hash 2_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3", "Debug Unlock PK Hash 2_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4", "Debug Unlock PK Hash 2_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5", "Debug Unlock PK Hash 2_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6", "Debug Unlock PK Hash 2_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7", "Debug Unlock PK Hash 2_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8", "Debug Unlock PK Hash 2_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9", "Debug Unlock PK Hash 2_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10", "Debug Unlock PK Hash 2_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11", "Debug Unlock PK Hash 2_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_3
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0", "Debug Unlock PK Hash 3_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1", "Debug Unlock PK Hash 3_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2", "Debug Unlock PK Hash 3_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3", "Debug Unlock PK Hash 3_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4", "Debug Unlock PK Hash 3_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5", "Debug Unlock PK Hash 3_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6", "Debug Unlock PK Hash 3_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7", "Debug Unlock PK Hash 3_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8", "Debug Unlock PK Hash 3_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9", "Debug Unlock PK Hash 3_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10", "Debug Unlock PK Hash 3_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11", "Debug Unlock PK Hash 3_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_4
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0", "Debug Unlock PK Hash 4_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1", "Debug Unlock PK Hash 4_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2", "Debug Unlock PK Hash 4_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3", "Debug Unlock PK Hash 4_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4", "Debug Unlock PK Hash 4_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5", "Debug Unlock PK Hash 4_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6", "Debug Unlock PK Hash 4_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7", "Debug Unlock PK Hash 4_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8", "Debug Unlock PK Hash 4_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9", "Debug Unlock PK Hash 4_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10", "Debug Unlock PK Hash 4_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11", "Debug Unlock PK Hash 4_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
      },

    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_5
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0", "Debug Unlock PK Hash 5_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1", "Debug Unlock PK Hash 5_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2", "Debug Unlock PK Hash 5_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3", "Debug Unlock PK Hash 5_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4", "Debug Unlock PK Hash 5_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5", "Debug Unlock PK Hash 5_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6", "Debug Unlock PK Hash 5_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7", "Debug Unlock PK Hash 5_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8", "Debug Unlock PK Hash 5_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9", "Debug Unlock PK Hash 5_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10", "Debug Unlock PK Hash 5_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11", "Debug Unlock PK Hash 5_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_6
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0", "Debug Unlock PK Hash 6_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1", "Debug Unlock PK Hash 6_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2", "Debug Unlock PK Hash 6_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3", "Debug Unlock PK Hash 6_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4", "Debug Unlock PK Hash 6_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5", "Debug Unlock PK Hash 6_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6", "Debug Unlock PK Hash 6_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7", "Debug Unlock PK Hash 6_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8", "Debug Unlock PK Hash 6_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9", "Debug Unlock PK Hash 6_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10", "Debug Unlock PK Hash 6_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11", "Debug Unlock PK Hash 6_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_DEBUG_UNLOCK_PK_HASH_7
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0", "Debug Unlock PK Hash 7_0", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1", "Debug Unlock PK Hash 7_1", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2", "Debug Unlock PK Hash 7_2", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3", "Debug Unlock PK Hash 7_3", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4", "Debug Unlock PK Hash 7_4", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5", "Debug Unlock PK Hash 7_5", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6", "Debug Unlock PK Hash 7_6", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7", "Debug Unlock PK Hash 7_7", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8", "Debug Unlock PK Hash 7_8", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9", "Debug Unlock PK Hash 7_9", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10", "Debug Unlock PK Hash 7_10", REG_CONFIG_DONE_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11", "Debug Unlock PK Hash 7_11", REG_CONFIG_DONE_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },
        
    // REG_GROUP_INTERRUPT_EN
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, "GLOBAL_INTR_EN_R", "Global Intrpt Enable", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R, "ERROR0_INTR_EN_R", "Err0 Intrpt Enable", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R, "ERROR1_INTR_EN_R", "Err1 Intrpt Enable", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R, "NOTIF0_INTR_EN_R", "Notification 0 Intrpt Enable", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R, "NOTIF1_INTR_EN_R", "Notification 1 Intrpt Enable", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R, "ERROR_GLOBAL_INTR_R", "Err Global Intrpt", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R, "NOTIF_GLOBAL_INTR_R", "Notification Global Intrpt", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_INTERRUPT_STATUS_RW1C
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, "ERROR0_INTERNAL_INTR_R", "Err0 Internal Intrpt", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R, "ERROR1_INTERNAL_INTR_R", "Err1 Internal Intrpt", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, "NOTIF0_INTERNAL_INTR_R", "Notification 0 Internal Intrpt", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R, "NOTIF1_INTERNAL_INTR_R", "Notification 1 Internal Intrpt", REG_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, "ERROR0_INTR_TRIG_R", "Err0 Internal Trigger", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, "ERROR1_INTR_TRIG_R", "Err1 Internal Trigger", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, "NOTIF0_INTR_TRIG_R", "Notification 0 Internal Trigger", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, "NOTIF1_INTR_TRIG_R", "Notification 1 Internal Trigger", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_INTERRUPT_ERROR0_COUNTERS
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R, "ERROR_INTERNAL_INTR_COUNT_R", "Err Internal Intrpt Count", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R, "ERROR_MBOX0_ECC_UNC_INTR_COUNT_R", "Err MBOX0 ECC Uncorrectable Intrpt Count", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R, "ERROR_MBOX1_ECC_UNC_INTR_COUNT_R", "Err MBOX1 ECC Uncorrectable Intrpt Count", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R, "ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R", "Err MCU SRAM DMI AXI Collision Intrpt Count", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R, "ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R", "Err WDT Timer1 Timeout Intrpt Count", REG_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R, "ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R", "Err WDT Timer2 Timeout Intrpt Count", REG_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_INTERRUPT_NOTIF0_COUNTERS
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R, "NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R", "Notification MCU SRAM ECC Correctable Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R, "NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R", "Notification CPTRA MCU Reset Request Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R, "NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R", "Notification General Input Toggle Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R, "NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R", "Notification MBOX0 Target Done Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R, "NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R", "Notification MBOX1 Target Done Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R, "NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R", "Notification MBOX0 Command Available Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R, "NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R", "Notification MBOX1 Command Available Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R, "NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R", "Notification CPTRA MBOX Command Available Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R, "NOTIF_MBOX0_ECC_COR_INTR_COUNT_R", "Notification MBOX0 ECC Correctable Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R, "NOTIF_MBOX1_ECC_COR_INTR_COUNT_R", "Notification MBOX1 ECC Correctable Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R, "NOTIF_DEBUG_LOCKED_INTR_COUNT_R", "Notification Debug Locked Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R, "NOTIF_SCAN_MODE_INTR_COUNT_R", "Notification Scan Mode Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R, "NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R", "Notification MBOX0 SOC Request Lock Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R, "NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R", "Notification MBOX1 SOC Request Lock Intrpt Count", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_OTP_OPERATION_DONE_INTR_COUNT_R, "NOTIF_OTP_OPERATION_DONE_INTR_COUNT_R", "Notification OTP Operation Done Intrpt Count", REG_NOT_STICKY, false} ,
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_TRACE
    {
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR, "MCU_TRACE_BUFFER_CSR_READ_PTR", "Trace Buffer Read Pointer", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_TRACE_RO
    {
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, "MCU_TRACE_BUFFER_CSR_STATUS", "Trace Buffer Status", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_CONFIG, "MCU_TRACE_BUFFER_CSR_CONFIG", "Trace Buffer Configuration", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_DATA, "MCU_TRACE_BUFFER_CSR_DATA", "Trace Buffer Data", REG_NOT_STICKY, false },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR, "MCU_TRACE_BUFFER_CSR_WRITE_PTR", "Trace Buffer Write Pointer", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    },

    // REG_GROUP_SOC_MBOX_CSR
    {
        { SOC_MBOX_CSR_MBOX_LOCK, "MBOX_LOCK", "Mailbox Lock", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_USER, "MBOX_USER", "Mailbox User", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_CMD, "MBOX_CMD", "Mailbox Command", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_DLEN, "MBOX_DLEN", "Mailbox Data Length", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_DATAIN, "MBOX_DATAIN", "Mailbox Data Input", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_DATAOUT, "MBOX_DATAOUT", "Mailbox Data Output", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_EXECUTE, "MBOX_EXECUTE", "Mailbox Execute", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_STATUS, "MBOX_STATUS", "Mailbox Status", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_MBOX_UNLOCK, "MBOX_UNLOCK", "Mailbox Unlock", REG_NOT_STICKY, false },
        { SOC_MBOX_CSR_TAP_MODE, "TAP_MODE", "TAP Mode", REG_NOT_STICKY, false },
        { 0, NULL, NULL, REG_NOT_STICKY, false }  // End marker
    }
};

/* Function to get a string representation of a register group */
const char* get_group_name(mci_register_group_t group) {
    switch(group) {
        case REG_GROUP_KNOWN_VALUES: return "Hardcoded Values";
        case REG_GROUP_CAPABILITIES: return "Capabilities";
        case REG_GROUP_CAPABILITIES_RO: return "Capabilities-RO";
        case REG_GROUP_STRAPS_RO: return "SS Straps RO";
        case REG_GROUP_STATUS: return "Status";
        case REG_GROUP_STATUS_RO: return "Status-RO";
        case REG_GROUP_SECURITY_RO: return "Security-RO";
        case REG_GROUP_ERROR_RW1C: return "Ftl/Non-Ftl err W1C";
        case REG_GROUP_ERROR: return "Ftl/Non-Ftl Err";
        case REG_GROUP_INTERNAL_ERROR_MASK: return "Internal err Mask";
        case REG_GROUP_WATCHDOG: return "Watchdog";
        case REG_GROUP_WATCHDOG_RO: return "Watchdog-RO";
        case REG_GROUP_MCU: return "MCU";
        case REG_GROUP_CONTROL: return "Control";
        case REG_GROUP_CONTROL_RO: return "Control RO (Tap Access RW in Debug Mode)";
        case REG_GROUP_MCI_MBOX0: return "MCI Mailbox 0 AXI User";
        case REG_GROUP_MCI_MBOX0_RW1S: return "MCI Mailbox 0 AXI User Lock";
        case REG_GROUP_MCU_MBOX0: return "MCU Mailbox 0";
        case REG_GROUP_MCU_MBOX0_RO: return "MCU Mailbox 0 - RO";
        case REG_GROUP_MCI_MBOX1: return "MCI Mailbox 1 AXI User";
        case REG_GROUP_MCI_MBOX1_RW1S: return "MCI Mailbox 1 AXI User Lock";
        case REG_GROUP_MCU_MBOX1: return "MCU Mailbox 1";
        case REG_GROUP_MCU_MBOX1_RO: return "MCU Mailbox 1 - RO";
        case REG_GROUP_DFT: return "DFT";
        case REG_GROUP_DEBUG: return "Debug";
        case REG_GROUP_GENERIC_WIRES: return "Generic Wires";
        case REG_GROUP_GENERIC_WIRES_RO: return "Generic Wires - RO";
        case REG_GROUP_SS: return "Subsystem";
        case REG_GROUP_SS_RO: return "Subsystem_RO";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_0: return "Debug Unlock PK Hash 0";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_1: return "Debug Unlock PK Hash 1";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_2: return "Debug Unlock PK Hash 2";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_3: return "Debug Unlock PK Hash 3";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_4: return "Debug Unlock PK Hash 4";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_5: return "Debug Unlock PK Hash 5";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_6: return "Debug Unlock PK Hash 6";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_7: return "Debug Unlock PK Hash 7";
        case REG_GROUP_INTERRUPT_EN: return "Intrpt Enable";
        case REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO: return "Intrpt Global Status RO";
        case REG_GROUP_INTERRUPT_STATUS_RW1C: return "Intrpt Status W1C";
        case REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S: return "Intrpt Trigger Pulse W1S";
        case REG_GROUP_INTERRUPT_ERROR0_COUNTERS: return "Err 0 Intrpt Counters";
        case REG_GROUP_INTERRUPT_NOTIF0_COUNTERS: return "Notif 0 Intrpt Counters";
        case REG_GROUP_TRACE: return "Trace";
        case REG_GROUP_TRACE_RO: return "Trace-RO";
        case REG_GROUP_SOC_MBOX_CSR: return "SOC Mailbox CSR";
        default: return "Unknown";
    }
}

/* Get the number of registers in a group */
int get_register_count(mci_register_group_t group) {
    int count = 0;
    
    if (group >= REG_GROUP_COUNT) {
        return 0;
    }
    
    while (register_groups[group][count].address != 0) {
        count++;
    }
    
    return count;
}

/* Get register information by its index within a group */
const mci_register_info_t* get_register_info(mci_register_group_t group, int index) {
    if (group >= REG_GROUP_COUNT) {
        return NULL;
    }
    
    if (index < 0 || index >= MAX_REGISTERS_PER_GROUP) {
        return NULL;
    }
    
    if (register_groups[group][index].address == 0) {
        return NULL;
    }
    
    return &register_groups[group][index];
}

/**
 * Function to find a register by address (across all groups)
 * 
 * @param address Register address
 * @param group_index Pointer to store group index
 * @param reg_index Pointer to store register index
 * @return Register info pointer, or NULL if not found
 */
const mci_register_info_t* find_register_by_address(uint32_t address, 
                                                   mci_register_group_t *group_index, 
                                                   int *reg_index) {
    for (int group = 0; group < REG_GROUP_COUNT; group++) {
        int count = get_register_count((mci_register_group_t)group);
        
        for (int i = 0; i < count; i++) {
            const mci_register_info_t *reg = get_register_info((mci_register_group_t)group, i);
            
            if (reg && reg->address == address) {
                if (group_index) *group_index = (mci_register_group_t)group;
                if (reg_index) *reg_index = i;
                return reg;
            }
        }
    }
    
    return NULL;

}

/**
 * Function to calculate the total number of registers across all groups
 * 
 * @return Total number of registers
 */
int get_total_register_count(void) {
    int total = 0;
    for (int group = 0; group < REG_GROUP_COUNT; group++) {
        total += get_register_count((mci_register_group_t)group);
    }
    return total;
}

/**
 * Initialize the register expected data dictionary
 * 
 * @param dict Pointer to dictionary to initialize
 */
void init_reg_exp_dict(mci_reg_exp_dict_t *dict) {
    VPRINTF(LOW, "Initializing expected data dict\n");
    dict->count = 0;

    // Add new entry if space available
    for (mci_register_group_t group = 0; group < REG_GROUP_COUNT; group++) {
        int count = get_register_count(group);

        VPRINTF(MEDIUM, "Initializing %d registers in group %s\n", count, get_group_name(group) );

        if (group == REG_GROUP_KNOWN_VALUES) {
            for (int i = 0; i < count; i++) {
                const mci_register_info_t *reg = get_register_info(group, i);
                VPRINTF(MEDIUM, "Init reg 0x%08x\n", reg->address);
                uint32_t known_value = get_known_register_value(reg->address);
                dict->entries[dict->count].address = reg->address;
                dict->entries[dict->count].expected_data = known_value;
                dict->count++;
            }
        } else {
            for (int i = 0; i < count; i++) {
                const mci_register_info_t *reg = get_register_info(group, i);
                VPRINTF(MEDIUM, "Init reg 0x%08x\n", reg->address);
                dict->entries[dict->count].address = reg->address;
                dict->entries[dict->count].expected_data = 0;
                dict->count++;
            }
        }
    }
}
/*
void reset_exp_reg_data(mci_reg_exp_dict_t *dict, reset_type_t reset_type, mci_register_group_t *groups, int num_groups) {
    if (reset_type == COLD_RESET ) {
        VPRINTF(LOW, "** Clearing all expected values for cold reset\n");
    } else if (reset_type == WARM_RESET) {
        VPRINTF(LOW, "** Clearing expected values for non-sticky registers\n");
    }

    // Create a bit mask for fast group lookup
    unsigned int group_mask = 0;
    for (int j = 0; j < num_groups; j++) {
        group_mask |= (1 << groups[j]);
    }

    mci_register_group_t group_index;
    int reg_index;
    const mci_register_info_t *reg_info;
    uint32_t read_intr0_sts;
    uint32_t read_intr1_sts;
    const mci_register_info_t *intr0_reg;
    const mci_register_info_t *intr1_reg;
    uint32_t value;
    uint32_t reset_value = 0xFFFFFFFF;

    for (int i = 0; i < dict->count; i++) {
        value = 0;
        reg_info = find_register_by_address(dict->entries[i].address, 
                                           &group_index, 
                                           &reg_index);
        
        if (reg_info) {
            VPRINTF(MEDIUM, "Found reg in dictionary\n");

            // Check if group is in the list
            bool group_in_list = (group_mask & (1 << group_index)) != 0;
            
            // Skip if the register group is not in the list
            if (!group_in_list) {
                continue;
            }


            // For cold reset, clear all entries
            if (reset_type == COLD_RESET) {
                if (group_index == REG_GROUP_MCI_MBOX0 || group_index == REG_GROUP_MCI_MBOX1) {
                    if (reg_index >=0 && reg_index < 5) {
                        dict->entries[i].expected_data = reset_value;
                    }
                    else {
                        dict->entries[i].expected_data = 0;
                    }
                } else if (group_index == REG_GROUP_WATCHDOG) {
                    if (reg_index == 2 || reg_index == 3 || reg_index == 6 || reg_index == 7) {
                        dict->entries[i].expected_data = reset_value;
                    } else {
                        dict->entries[i].expected_data = 0;
                    }
                } else {
                    dict->entries[i].expected_data = 0;
                }   
            } 
            // For warm reset, only clear non-sticky registers
            else if (reset_type == WARM_RESET && reg_info->is_sticky == REG_NOT_STICKY) {
                if (group_index == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO) {
                    if (reg_index == 0) {
                        intr0_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 0);
                        intr1_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 1);
                        read_intr0_sts = mci_reg_read(intr0_reg->address);
                        read_intr1_sts = mci_reg_read(intr1_reg->address);
                        if (read_intr0_sts != 0) {
                            value |= MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_MASK;
                        }
                        if (read_intr1_sts != 0) {
                            value |= MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_MASK;
                        }
                        dict->entries[i].expected_data = value;
                    }
                    else {
                        intr0_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 2);
                        intr1_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 3);
                        read_intr0_sts = mci_reg_read(intr0_reg->address);
                        read_intr1_sts = mci_reg_read(intr1_reg->address);
                        if (read_intr0_sts != 0) {
                            value |= MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_MASK;
                        }
                        if (read_intr1_sts != 0) {
                            value |= MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_MASK;
                        }
                        dict->entries[i].expected_data = value;
                    }
                } else {      
                    dict->entries[i].expected_data = 0;
                }
            }
        } 
    }
}
*/

/**
 * Add or update an entry in the register expected data dictionary
 * 
 * @param dict Pointer to dictionary
 * @param address Register address (key)
 * @param name Register name
 * @param value Expected data value
 * @param mask Mask to apply to the value
 * @return 0 on success, -1 if dictionary is full
 */
 int set_reg_exp_data(mci_reg_exp_dict_t *dict, uint32_t address, uint32_t value, uint32_t mask, bool reg_write) {

    VPRINTF(MEDIUM, "UPDATE REG [0x%0x] with Value = 0x%0x, Mask = 0x%0x\n", address, value, mask);

    // Check if CONFIG_DONE_STICKY is set; If set, expected value = previous value
    uint32_t ss_config_done_sticky;
    const mci_register_info_t *ss_config_done_sticky_reg = get_register_info(REG_GROUP_SS, 0);
    ss_config_done_sticky = mci_reg_read(ss_config_done_sticky_reg->address);

    uint32_t ss_config_done;
    const mci_register_info_t *ss_config_done_reg = get_register_info(REG_GROUP_SS, 1);
    ss_config_done = mci_reg_read(ss_config_done_reg->address);


    mci_register_group_t group_index;
    int reg_index;
    const mci_register_info_t *reg_info;
    const mci_register_info_t *intr_glb_sts_reg;
    const mci_register_info_t *intr_sts_reg;
    const mci_register_info_t *axi_user_lock_reg;
    const mci_register_info_t *capabilities_reg;
    const mci_register_info_t *cap_lock_reg;
    uint32_t glb_sts_mask;
    uint32_t intr_sts_mask;
    uint32_t err_data;
    uint32_t read_intr_sts;
    uint32_t axi_user_lock;
    uint32_t cap_lock_reg_value = 0;
    bool update_axi_user = false;
    bool update_config_reg = false;
    bool update_cap_lock_reg = false;
    bool reset_reason_reg = false;
    bool update_exp_data = false;

    reg_info = find_register_by_address(address, &group_index, &reg_index);
    VPRINTF(MEDIUM, "Register Name = %s\n", reg_info->name);
    
    if (group_index == REG_GROUP_ERROR_RW1C || group_index == REG_GROUP_INTERRUPT_STATUS_RW1C) {
        err_data = mci_reg_read(address);
        if (reg_write) {
            value = err_data & ~value;
        }
        VPRINTF(MEDIUM, "Read current register data = 0x%0x\n", err_data);
    }

    if (group_index == REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S) {
        intr_sts_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, reg_index);
        read_intr_sts = mci_reg_read(intr_sts_reg->address);
        intr_sts_mask = get_register_mask(intr_sts_reg->address);
    
        if (reg_index == 0 || reg_index == 1) {
            intr_glb_sts_reg = get_register_info(REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO, 0);
            if (reg_index == 0) {
                glb_sts_mask = MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_MASK;
            }
            else {
                glb_sts_mask = MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_MASK;
            }
        } else if (reg_index == 2 || reg_index == 3) {
            intr_glb_sts_reg = get_register_info(REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO, 1);
            if (reg_index == 2) {
                glb_sts_mask = MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_MASK;
            }
            else {
                glb_sts_mask = MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_MASK;
            }
        }
    }

    if (group_index == REG_GROUP_MCI_MBOX0) {
        axi_user_lock_reg = get_register_info(REG_GROUP_MCI_MBOX0_RW1S, reg_index);
        axi_user_lock = mci_reg_read(axi_user_lock_reg->address);
        if (axi_user_lock == 0) {
            update_axi_user = true;
        }
    }

    if (group_index == REG_GROUP_MCI_MBOX1) {
        axi_user_lock_reg = get_register_info(REG_GROUP_MCI_MBOX1_RW1S, reg_index);
        axi_user_lock = mci_reg_read(axi_user_lock_reg->address);
        if (axi_user_lock == 0) {
            update_axi_user = true;
        }
    }

    if (group_index == REG_GROUP_CAPABILITIES) {
        if (reg_index <= 1) {
            cap_lock_reg = get_register_info(REG_GROUP_CAPABILITIES, 2);
            cap_lock_reg_value = mci_reg_read(cap_lock_reg->address);
            if (cap_lock_reg_value == 0) {
                update_config_reg = true;
            }
        } else if (reg_index == 2) {
            if (ss_config_done == 0) {
                update_cap_lock_reg = true;
            }
        }   
    }

    /*
    if (group_index == REG_GROUP_CAPABILITIES && reg_index <= 2) {
        capabilities_reg = get_register_info(REG_GROUP_CAPABILITIES, reg_index);
        if (ss_config_done == 0) {
            update_config_reg = true;
        }
    }
    */


    // Special handling as stickiness is different for different fields
    //if (reg_info->address == SOC_MCI_TOP_MCI_REG_RESET_REASON) {
    //    reset_reason_reg = true;
    //}


    bool force_update = (address == SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE_STICKY);
    
    // Standard update condition
    if (ss_config_done_sticky == 0 || reg_info->is_sticky != REG_CONFIG_DONE_STICKY || force_update || update_axi_user || update_config_reg || update_cap_lock_reg) {
    	update_exp_data = true;
    }

    // Special case for capabilities registers - override the above conditions
    if (group_index == REG_GROUP_CAPABILITIES && reg_index <= 2 && cap_lock_reg_value == 1) {
        update_exp_data = false;  // Block update regardless of other conditions
        VPRINTF(MEDIUM, "Capabilities REG %d, cap lock = %d, update_exp_data = %d\n", reg_index, cap_lock_reg_value, update_exp_data);
    }
    

    bool pulse_timer_reg = (address == SOC_MCI_TOP_MCI_REG_WDT_TIMER1_CTRL || address == SOC_MCI_TOP_MCI_REG_WDT_TIMER2_CTRL);
    bool pulse_intr_reg = (group_index == REG_GROUP_INTERRUPT_TRIGGER_PULSE_RW1S);
    
    // First check if entry already exists
    for (int i = 0; i < dict->count; i++) {
        if (dict->entries[i].address == address) {
            VPRINTF(MEDIUM, "Entry exists!\n");
            // Update existing entry's expected data only if sticky bit is NOT set
            //if (ss_config_done_sticky == 0 || reg_info->is_sticky != REG_CONFIG_DONE_STICKY || force_update || update_axi_user || update_config_reg) {
	        if (update_exp_data) {
                //if (reset_reason_reg) {
                //    VPRINTF(MEDIUM, "Only [1:0] is not sticky\n");
                //    dict->entries[i].expected_data = value & (MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK | MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK);
                //} else 
                if (!pulse_timer_reg && !pulse_intr_reg) {
                    VPRINTF(MEDIUM, "Not pulse reg, value = 0x%0x\n", value & mask);
                    dict->entries[i].expected_data = value & mask;
                } else if (pulse_timer_reg) {
                    VPRINTF(MEDIUM, "Pulse Timer reg, value = 0x0\n");
                    dict->entries[i].expected_data = 0x0;
                } else {
                    VPRINTF(MEDIUM, "Pulse Interrupt reg, value = 0x0\n");
                    dict->entries[i].expected_data = 0x0;
                    // Update expected data for corresponding interrupt status register
                    VPRINTF(MEDIUM, "Recursively Updating exp_data for %s [ 0x%0x ] = 0x%0x (read_intr_sts)\n", intr_sts_reg->name, intr_sts_reg->address, read_intr_sts);
                    set_reg_exp_data(dict, intr_sts_reg->address, read_intr_sts, intr_sts_mask, false);
                    // Update global interrupt status register
                    set_reg_exp_data(dict, intr_glb_sts_reg->address, (1U << (glb_sts_mask - 1)), glb_sts_mask, false);
                } 
            }
            // If sticky bit is set, retain previous expected value (do nothing)
            
            return 0; // Return after handling existing entry
        }
    }
    
    // Add new entry if space available
    if (dict->count < MAX_REGISTER_ENTRIES) {
        dict->entries[dict->count].address = address;
        //if (reset_reason_reg) {
        //    VPRINTF(MEDIUM, "Only [1:0] is not sticky\n");
        //    dict->entries[dict->count].expected_data = value & (MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK | MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK);
        //} else 
        if (!pulse_timer_reg && !pulse_intr_reg) {
            VPRINTF(MEDIUM, "Not pulse reg, value = 0x%0x\n", value & mask);
            dict->entries[dict->count].expected_data = value & mask;
        } else if (pulse_timer_reg) {
            VPRINTF(MEDIUM, "Pulse reg, value = 0x0\n");
            dict->entries[dict->count].expected_data = 0x0;
        }
        else {
            VPRINTF(MEDIUM, "Pulse Interrupt reg, value = 0x0\n");
            dict->entries[dict->count].expected_data = 0x0;
            // Update expected data for corresponding interrupt status register
            set_reg_exp_data(dict, intr_sts_reg->address, read_intr_sts, intr_sts_mask, false);
            // Update global interrupt status register
            set_reg_exp_data(dict, intr_glb_sts_reg->address, (1U << (glb_sts_mask - 1)), glb_sts_mask, false);
        }
        dict->count++;
        return 0;
    }
    
    return -1; // Dictionary full
}

/**
 * Get expected data for a register
 * 
 * @param dict Pointer to dictionary
 * @param address Register address to lookup
 * @param value Pointer to store expected value
 * @return 0 if found, -1 if not found
 */
int get_reg_exp_data(mci_reg_exp_dict_t *dict, uint32_t address, uint32_t *value) {
    for (int i = 0; i < dict->count; i++) {
        if (dict->entries[i].address == address) {
            if (value) {
                *value = dict->entries[i].expected_data;
            }
            return 0;
        }
    }
    
    return -1; // Not found
}

/**
 * Get known value for a register with REG_ACCESS_KNOWN type
 */
uint32_t get_known_register_value(uint32_t reg_addr) {
    switch (reg_addr) {
        case SOC_MCI_TOP_MCI_REG_HW_REV_ID:
            return 0x00002001;  // SS Version 2.0.1
            
        default:
            return 0x00000000;
    }
}

/**
 * Convert a register address to a bitmap index and bit position
 * 
 * @param reg_addr Register address
 * @param word_index Pointer to store the word index in the bitmap
 * @param bit_position Pointer to store the bit position in the word
 */
static void address_to_bitmap_position(uint32_t reg_addr, uint32_t *word_index, uint32_t *bit_position) {
    // Use the lower bits of the address as a simple hash
    // This works because register addresses are typically aligned and spaced apart
    uint32_t hash_value = reg_addr & ((1 << ADDRESS_BITS_FOR_INDEXING) - 1);
    
    *word_index = hash_value / 32;
    *bit_position = hash_value % 32;
}

/**
 * Exclude a register by its address with collision handling
 * 
 * @param reg_addr Register address to exclude
 * @return 0 on success, -1 if collision table is full
 */
int exclude_register(uint32_t reg_addr) {
    uint32_t word_index, bit_position;
    
    // Compute position in bitmap
    address_to_bitmap_position(reg_addr, &word_index, &bit_position);
    
    // Set the bit in the bitmap
    excluded_registers_bitmap[word_index] |= (1UL << bit_position);
    
    // Add to collision table
    if (collision_count < MAX_EXCLUDED_REGISTERS) {
        collision_table[collision_count++] = reg_addr;
        return 0;
    }
    
    // Collision table is full
    printf("WARNING: Collision table full, cannot add register 0x%08x\n", reg_addr);
    return -1;
}

/**
 * Check if a register is excluded with collision handling
 * 
 * @param reg_addr Register address to check
 * @return 1 if excluded, 0 otherwise
 */
int is_register_excluded(uint32_t reg_addr) {
    uint32_t word_index, bit_position;
    
    // Compute position in bitmap
    address_to_bitmap_position(reg_addr, &word_index, &bit_position);
    
    // First, check the bit in the bitmap
    if (excluded_registers_bitmap[word_index] & (1UL << bit_position)) {
        // Potential match, verify in collision table to handle hash collisions
        for (int i = 0; i < collision_count; i++) {
            if (collision_table[i] == reg_addr) {
                return 1;  // Confirmed match in collision table
            }
        }
    }
    
    return 0;  // Not excluded
}

/**
 * Initialize the excluded registers bitmap
 */
void init_excluded_registers(void) {

    VPRINTF(LOW, "Initialize excluded registers\n");
    // Clear the bitmap and collision table
    memset(excluded_registers_bitmap, 0, sizeof(excluded_registers_bitmap));
    memset(collision_table, 0, sizeof(collision_table));
    collision_count = 0;
    
    // Define the excluded registers
    //exclude_register(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO);
    //exclude_register(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    //exclude_register(SOC_MBOX_CSR_MBOX_LOCK);
    //exclude_register(SOC_MBOX_CSR_MBOX_USER);
    
    // Add any other registers that should be excluded
    // exclude_register(...);
}


void write_random_to_register_group_and_track(mci_register_group_t group, mci_reg_exp_dict_t *dict) {
    int count = get_register_count(group);
    VPRINTF(LOW, "Writing random values to all %s registers (%d total):\n", get_group_name(group), count);

    bool ro_reg = false;
    if (group == REG_GROUP_KNOWN_VALUES ||
        group == REG_GROUP_CAPABILITIES_RO ||
        group == REG_GROUP_STRAPS_RO ||
        group == REG_GROUP_STATUS_RO ||
        group == REG_GROUP_SECURITY_RO ||
        group == REG_GROUP_WATCHDOG_RO ||
        group == REG_GROUP_MCU_MBOX0_RO ||
        group == REG_GROUP_MCU_MBOX1_RO ||
        group == REG_GROUP_GENERIC_WIRES_RO ||
        group == REG_GROUP_SS_RO) {
            ro_reg = true;
        }
    
    for (int i = 0; i < count; i++) {
        const mci_register_info_t *reg = get_register_info(group, i);
        
        if (reg) {
            // Check if this register should be excluded using our efficient method
            if (!is_register_excluded(reg->address)) {
                // Generate a unique value for each register
                uint32_t rand_value = xorshift32();
            
                VPRINTF(MEDIUM, "  Writing 0x%08x to %s (0x%08x)\n", rand_value, reg->name, reg->address);
                mci_reg_write(reg->address, rand_value);
                
                /* Get mask for this register */
                uint32_t mask = get_register_mask(reg->address);
                
                // Store in dictionary
                if (!ro_reg) {
                    if (set_reg_exp_data(dict, reg->address, rand_value, mask, true) != 0) {
                        VPRINTF(MEDIUM, "  WARNING: Could not store expected data for %s\n", reg->name);
                    }
                }
            } else {
                VPRINTF(MEDIUM, "  Skipping excluded register %s (0x%08x)\n", reg->name, reg->address);
            }
        }
    }
}

void write_to_register_group_and_track(mci_register_group_t group, uint32_t write_data, mci_reg_exp_dict_t *dict) {
    int count = get_register_count(group);
    VPRINTF(LOW, "Writing fixed value to all %s registers (%d total):\n", get_group_name(group), count);
    
    for (int i = 0; i < count; i++) {
        const mci_register_info_t *reg = get_register_info(group, i);
        
        if (reg) {
            // Check if this register should be excluded using our efficient method
            if (!is_register_excluded(reg->address)) {
                           
                VPRINTF(MEDIUM, "  Writing 0x%08x to %s (0x%08x)\n", write_data, reg->name, reg->address);
                mci_reg_write(reg->address, write_data);
                
                /* Get mask for this register */
                uint32_t mask = get_register_mask(reg->address);
                
                // Store in dictionary
                if (set_reg_exp_data(dict, reg->address, write_data, mask, true) != 0) {
                    VPRINTF(MEDIUM, "  WARNING: Could not store expected data for %s\n", reg->name);
                }
            } else {
                VPRINTF(MEDIUM, "  Skipping excluded register %s (0x%08x)\n", reg->name, reg->address);
            }
        }
    }
}

/**
 * Function to read all registers in a group and verify their values against expected data
 * 
 * @param group Register group
 * @param dict Dictionary containing expected register values
 * @return Number of registers that failed verification
 */
int read_register_group_and_verify(mci_register_group_t group, mci_reg_exp_dict_t *dict, bool reset, reset_type_t reset_type) {
    uint32_t read_data;
    int count = get_register_count(group);
    int mismatch_count = 0;
    uint32_t exp_data;
    uint32_t read_intr0_sts;
    uint32_t read_intr1_sts;
    const mci_register_info_t *intr0_reg;
    const mci_register_info_t *intr1_reg;

    bool ro_reg = false;
    if (group == REG_GROUP_KNOWN_VALUES ||
        group == REG_GROUP_CAPABILITIES_RO ||
        group == REG_GROUP_STRAPS_RO ||
        group == REG_GROUP_STATUS_RO ||
        group == REG_GROUP_SECURITY_RO ||
        group == REG_GROUP_WATCHDOG_RO ||
        group == REG_GROUP_MCU_MBOX0_RO ||
        group == REG_GROUP_MCU_MBOX1_RO ||
        group == REG_GROUP_GENERIC_WIRES_RO ||
        group == REG_GROUP_SS_RO) {
            ro_reg = true;
        }
    
    VPRINTF(LOW, "Reading and verifying %s registers (%d total):\n", get_group_name(group), count);
    
    for (int i = 0; i < count; i++) {
        const mci_register_info_t *reg = get_register_info(group, i);
        
        if (reg) {
            // Skip excluded registers with collision-aware check
            if (is_register_excluded(reg->address)) {
                VPRINTF(MEDIUM, "  Skipping excluded register %s (0x%08x)\n", reg->name, reg->address);
                continue;
            }
            VPRINTF(MEDIUM,"Reg %s [0x%0x]\n", reg->name, reg->address);

            // Read the register value
            read_data = mci_reg_read(reg->address);
            
            // Get expected data from dictionary
            if (reset) {
                if (reset_type == COLD_RESET) {
                    if (reg->has_init_value == false && ro_reg == false) {
                        exp_data  = 0;
                        if (reg->address == SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H || reg->address == SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L && read_data >= exp_data) {
                            VPRINTF(MEDIUM, "  Expect reg increment: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data); 
                        } else if (read_data == exp_data) {
                            VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                        } else if (reg->address == SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) {
                            if (mci_reg_read(SOC_MCI_TOP_MCI_REG_SECURITY_STATE) & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) {
                                exp_data |= MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK;
                            }
                            if (mci_reg_read(SOC_MCI_TOP_MCI_REG_SECURITY_STATE) & MCI_REG_SECURITY_STATE_SCAN_MODE_MASK) {
                                exp_data |= MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK;
                            }
                        } 
                        else if (reg->address == SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R &&
                                    mci_reg_read(SOC_MCI_TOP_MCI_REG_SECURITY_STATE) & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) {
                            exp_data = 0x1;
                        } else {
                            VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                            mismatch_count++;
                        }
                    } else if (reg->has_init_value == false && ro_reg == true) {
                        if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                            if (read_data == exp_data) {
                                VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                       reg->name, reg->address, read_data, exp_data);
                            } else {
                                VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                       reg->name, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        } else {
                            VPRINTF(LOW, "  ! %s (0x%08x): Read 0x%08x, No expected data in dictionary\n", 
                                   reg->name, reg->address, read_data);
                        }
                    } else {
                        size_t init_array_size = sizeof(reg_init_values) / sizeof(reg_init_values[0]);
                        for (size_t i = 0; i < init_array_size; i++) {
                            if (reg_init_values[i].address == reg->address) {
                                exp_data = reg_init_values[i].default_value;
                                break;
                            }
                        }
                        if (read_data == exp_data) {
                            VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                        } else {
                            VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                            mismatch_count++;
                        }
                    }
                } else if (reset_type == WARM_RESET) {
                    if (reg->is_sticky == REG_STICKY || reg->is_sticky == REG_CONFIG_DONE_STICKY) {
                        if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                            VPRINTF(MEDIUM, "Expected data for %s = 0x%0x\n", reg->name, exp_data);
                            // Compare and report
                            if (group == REG_GROUP_INTERRUPT_ERROR0_COUNTERS) {
                                if ((i == 0 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_STS_MASK)) ||
                                    (i == 1 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK)) ||
                                    (i == 2 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK)) ||
                                    (i == 3 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_MASK)) ||
                                    (i == 4 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK)) ||
                                    (i == 5 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK))) {
                                    if (read_data >= exp_data) {
                                        VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x > Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                    } else {
                                        VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                        mismatch_count++;
                                    } 
                                }
                            } else if (reg->address == SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) {
                                exp_data |= MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK; // debug_locked_en_sts is set on Warm Reset
                            } else if (reg->address == SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R) {
                                exp_data = 0;
                            } else if (reg->address == SOC_MCI_TOP_MCI_REG_RESET_REASON) {
                                exp_data = exp_data & ~(MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK | MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK) | MCI_REG_RESET_REASON_WARM_RESET_MASK; // bits 0 & 1 are not sticky
                                if (read_data == exp_data) {
                                    VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n",reg->name, reg->address, read_data, exp_data); 
                                } else {
                                    VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                    mismatch_count++;
                                }
                            } else if (read_data == exp_data) {
                                VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                       reg->name, reg->address, read_data, exp_data);
                            } else if (read_data > exp_data && reg->address == SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H || reg->address == SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L) { 
                                VPRINTF(MEDIUM, "  Expect reg increment: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                        reg->name, reg->address, read_data, exp_data); 
                            } else {
                                VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                       reg->name, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        } else {
                            VPRINTF(LOW, "  ! %s (0x%08x): Read 0x%08x, No expected data in dictionary\n", 
                                   reg->name, reg->address, read_data);
                        }
                    } else {
                        if (reg->has_init_value == false && ro_reg == false) {
                            exp_data  = 0;
                            
                            if (read_data == exp_data) {
                                VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                            } else if (group == REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO) {
                                if (i == 0) {
                                    intr0_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 0);
                                    intr1_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 1);
                                    read_intr0_sts = mci_reg_read(intr0_reg->address);
                                    read_intr1_sts = mci_reg_read(intr1_reg->address);
                                    if (read_intr0_sts != 0) {
                                        exp_data |= MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_MASK;
                                    }
                                    if (read_intr1_sts != 0) {
                                        exp_data |= MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_MASK;
                                    }
                                } else {
                                    intr0_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 2);
                                    intr1_reg = get_register_info(REG_GROUP_INTERRUPT_STATUS_RW1C, 3);
                                    read_intr0_sts = mci_reg_read(intr0_reg->address);
                                    read_intr1_sts = mci_reg_read(intr1_reg->address);
                                    if (read_intr0_sts != 0) {
                                        exp_data |= MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_MASK;
                                    }
                                    if (read_intr1_sts != 0) {
                                        exp_data |= MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_MASK;
                                    }
                                }
                                if (read_data == exp_data) {
                                    VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                }
                                else {
                                    VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                    mismatch_count++;
                                }
                            } else if (group == REG_GROUP_INTERRUPT_NOTIF0_COUNTERS) {
                                if ((i == 0 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_MASK)) ||
                                    (i == 1 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK)) ||
                                    (i == 2 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK)) ||
                                    (i == 3 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_TARGET_DONE_STS_MASK)) ||
                                    (i == 4 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_TARGET_DONE_STS_MASK)) ||
                                    (i == 5 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK)) ||
                                    (i == 6 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_CMD_AVAIL_STS_MASK)) ||
                                    (i == 7 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_STS_MASK)) ||
                                    (i == 8 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_MASK)) ||
                                    (i == 9 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_ECC_COR_STS_MASK)) ||
                                    (i == 10 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)) ||
                                    (i == 11 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK)) ||
                                    (i == 12 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_MASK)) ||
                                    (i == 13 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_SOC_REQ_LOCK_STS_MASK)) ||
                                    (i == 14 && (mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R) & MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_OTP_OPERATION_DONE_STS_MASK))) {
                                    if (read_data >= exp_data) {
                                        VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x > Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                    } else {
                                        VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                    mismatch_count++;
                                    }
                                } 
                            } else {
                                VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        } else if (reg->has_init_value == false && ro_reg == true) {
                            if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                                if (read_data == exp_data) {
                                    VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                           reg->name, reg->address, read_data, exp_data);
                                } else {
                                    VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                           reg->name, reg->address, read_data, exp_data);
                                    mismatch_count++;
                                }
                            } else {
                                VPRINTF(LOW, "  ! %s (0x%08x): Read 0x%08x, No expected data in dictionary\n", 
                                       reg->name, reg->address, read_data);
                            }
                        } else {
                            size_t init_array_size = sizeof(reg_init_values) / sizeof(reg_init_values[0]);
                            for (size_t i = 0; i < init_array_size; i++) {
                                if (reg_init_values[i].address == reg->address) {
                                    exp_data = reg_init_values[i].default_value;
                                    break;
                                }
                            }
                            if (read_data == exp_data) {
                                VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                            } else {
                                VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", reg->name, reg->address, read_data, exp_data);
                                mismatch_count++;
                            }
                        }
                    }
                } 
            } else { // Verifying after a write operation
                if (get_reg_exp_data(&g_expected_data_dict, reg->address, &exp_data) == 0) {
                    // Compare and report
                    if (read_data == exp_data) {
                        VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                            reg->name, reg->address, read_data, exp_data);
                    } else if (read_data > exp_data && reg->address == SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H || reg->address == SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L) { 
                        VPRINTF(MEDIUM, "  Expect reg increment: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                                reg->name, reg->address, read_data, exp_data); 
                    } else {
                        VPRINTF(LOW, "  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                            reg->name, reg->address, read_data, exp_data);
                        mismatch_count++;
                    }
                } else {
                    VPRINTF(LOW, "  ! %s (0x%08x): Read 0x%08x, No expected data in dictionary\n", 
                        reg->name, reg->address, read_data);
                }
            } 
        } else {
            VPRINTF(LOW, "  ! Register index %d not found in group\n", i);
        }
    }
    
    VPRINTF(LOW, "Verification complete: %d register(s) matched, %d register(s) mismatched\n", 
           count - mismatch_count, mismatch_count);
    
    return mismatch_count;
}

/**
 * Function to read all registers in a group and track their values in a dictionary
 * 
 * @param group Register group
 * @param dict Dictionary to store register values
 */
void read_register_group_and_track(mci_register_group_t group, mci_reg_exp_dict_t *dict) {
    uint32_t read_data;
    int count = get_register_count(group);
    
    VPRINTF(LOW, "Reading and tracking %s registers (%d total):\n", get_group_name(group), count);
    
    for (int i = 0; i < count; i++) {
        const mci_register_info_t *reg = get_register_info(group, i);
        
        if (reg) {
            // Check if this register should be excluded
            if (!is_register_excluded(reg->address)) {
                // Read the register value
                read_data = mci_reg_read(reg->address);
                
                VPRINTF(MEDIUM, "  Reading 0x%08x from %s (0x%08x)\n", read_data, reg->name, reg->address);
                
                /* Get mask for this register */
                uint32_t mask = get_register_mask(reg->address);
                
                // Store in dictionary
                if (set_reg_exp_data(dict, reg->address, read_data, mask, false) != 0) {
                    VPRINTF(LOW, "  WARNING: Could not store read data for %s\n", reg->name);
                }
            } else {
                VPRINTF(MEDIUM, "  Skipping excluded register %s (0x%08x)\n", reg->name, reg->address);
            }
        }
    }
    
    VPRINTF(LOW, "Register tracking complete: %d register(s) read and tracked\n", count);
}


void init_mask_dict(void) {
    VPRINTF(LOW, "Initializing mask dict\n");
    g_mask_dict.count = 0;
    
    // SOC_MCI_TOP_MCI_REG_CAP_LOCK
    add_mask_entry(SOC_MCI_TOP_MCI_REG_CAP_LOCK,
                   MCI_REG_CAP_LOCK_LOCK_MASK);

    /* HW_REV_ID - has a mask for the MC_GENERATION field */
    add_mask_entry(SOC_MCI_TOP_MCI_REG_HW_REV_ID, 
                   MCI_REG_HW_REV_ID_MC_GENERATION_MASK);

    /* FW_REV_ID_0 - no masks defined, assume all bits can be used */
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_REV_ID_0, 0xFFFFFFFF);

    /* FW_REV_ID_1 - no masks defined, assume all bits can be used */
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_REV_ID_1, 0xFFFFFFFF);

    // HW_CONFIG0
    add_mask_entry(SOC_MCI_TOP_MCI_REG_HW_CONFIG0, 
                   MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_MASK | 
                   MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_MASK);

    // HW_CONFIG1
    add_mask_entry(SOC_MCI_TOP_MCI_REG_HW_CONFIG1, 
                   MCI_REG_HW_CONFIG1_MIN_MCU_RST_COUNTER_WIDTH_MASK | 
                   MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_MASK);

    // HW_FLOW_STATUS
    add_mask_entry(SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS,
                   MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK);

    // RESET_REASON
    add_mask_entry(SOC_MCI_TOP_MCI_REG_RESET_REASON,
                   MCI_REG_RESET_REASON_FW_HITLESS_UPD_RESET_MASK |
                   MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK |
                   MCI_REG_RESET_REASON_WARM_RESET_MASK);

    // RESET_STATUS
    add_mask_entry(SOC_MCI_TOP_MCI_REG_RESET_STATUS,
                   MCI_REG_RESET_STATUS_CPTRA_RESET_STS_MASK |
                   MCI_REG_RESET_STATUS_MCU_RESET_STS_MASK);

    // SECURITY_STATE
    add_mask_entry(SOC_MCI_TOP_MCI_REG_SECURITY_STATE,
                   MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK |
                   MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK |
                   MCI_REG_SECURITY_STATE_SCAN_MODE_MASK);

    // HW_ERROR_FATAL
    add_mask_entry(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL,
                   MCI_REG_HW_ERROR_FATAL_MCU_SRAM_ECC_UNC_MASK |
                   MCI_REG_HW_ERROR_FATAL_NMI_PIN_MASK |
                   MCI_REG_HW_ERROR_FATAL_MCU_SRAM_DMI_AXI_COLLISION_MASK);               

    // AGG_ERROR_FATAL
    add_mask_entry(SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL,
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL31_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL30_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL29_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL28_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL27_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL26_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL25_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL24_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL23_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL22_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL21_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL20_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL19_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL18_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL17_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL16_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL15_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL14_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL13_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL12_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL11_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL10_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL9_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL8_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL7_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL6_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL5_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL4_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL3_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL2_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL1_MASK |
                MCI_REG_AGG_ERROR_FATAL_AGG_ERROR_FATAL0_MASK);

    // HW_ERROR_NON_FATAL
    add_mask_entry(SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL,
                MCI_REG_HW_ERROR_NON_FATAL_MBOX0_ECC_UNC_MASK |
                MCI_REG_HW_ERROR_NON_FATAL_MBOX1_ECC_UNC_MASK);

    // AGG_ERROR_NON_FATAL
    add_mask_entry(SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL,
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL31_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL30_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL29_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL28_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL27_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL26_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL25_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL24_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL23_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL22_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL21_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL20_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL19_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL18_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL17_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL16_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL15_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL14_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL13_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL12_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL11_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL10_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL9_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL8_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL7_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL6_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL5_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL4_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL3_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL2_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL1_MASK |
                MCI_REG_AGG_ERROR_NON_FATAL_AGG_ERROR_NON_FATAL0_MASK);

    // FW_ERROR_FATAL (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_ERROR_FATAL, 0);

    // FW_ERROR_NON_FATAL (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_ERROR_NON_FATAL, 0);

    // HW_ERROR_ENC (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_HW_ERROR_ENC, 0);

    // FW_ERROR_ENC (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_ERROR_ENC, 0);

    // FW_EXTENDED_ERROR_INFO_0 (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_0, 0);

    // FW_EXTENDED_ERROR_INFO_1 (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_1, 0);

    // FW_EXTENDED_ERROR_INFO_2 (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_2, 0);

    // FW_EXTENDED_ERROR_INFO_3 (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_3, 0);

    // FW_EXTENDED_ERROR_INFO_4 (no masks defined)
    /////add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_4, 0);

    // FW_EXTENDED_ERROR_INFO_5 (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_5, 0);

    // FW_EXTENDED_ERROR_INFO_6 (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_6, 0);

    // FW_EXTENDED_ERROR_INFO_7 (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_7, 0);

    // INTERNAL_HW_ERROR_FATAL_MASK
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK,
                MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_ECC_UNC_MASK |
                MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK |
                MCI_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_MCU_SRAM_DMI_AXI_COLLISION_MASK);

    // INTERNAL_HW_ERROR_NON_FATAL_MASK
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK,
                MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX0_ECC_UNC_MASK |
                MCI_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX1_ECC_UNC_MASK);

    // INTERNAL_AGG_ERROR_FATAL_MASK
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK,
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL31_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL30_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL29_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL28_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL27_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL26_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL25_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL24_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL23_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL22_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL21_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL20_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL19_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL18_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL17_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL16_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL15_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL14_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL13_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL12_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL11_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL10_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL9_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL8_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL7_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL6_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL5_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL4_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL3_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL2_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL1_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_FATAL_MASK_MASK_AGG_ERROR_FATAL0_MASK);

    // INTERNAL_AGG_ERROR_NON_FATAL_MASK
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK,
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL31_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL30_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL29_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL28_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL27_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL26_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL25_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL24_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL23_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL22_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL21_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL20_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL19_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL18_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL17_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL16_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL15_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL14_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL13_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL12_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL11_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL10_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL9_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL8_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL7_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL6_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL5_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL4_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL3_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL2_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL1_MASK |
                MCI_REG_INTERNAL_AGG_ERROR_NON_FATAL_MASK_MASK_AGG_ERROR_NON_FATAL0_MASK);

    // INTERNAL_FW_ERROR_FATAL_MASK (no masks defined)
    //add_mask_entry(SOC_MCI_TOP_MCI_REG_INTERNAL_FW_ERROR_FATAL_MASK, 0);

    // WDT_TIMER1_EN
    add_mask_entry(SOC_MCI_TOP_MCI_REG_WDT_TIMER1_EN,
                MCI_REG_WDT_TIMER1_EN_TIMER1_EN_MASK);

    // WDT_TIMER1_CTRL
    add_mask_entry(SOC_MCI_TOP_MCI_REG_WDT_TIMER1_CTRL,
                MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK);

    // WDT_TIMER2_EN
    add_mask_entry(SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN,
                MCI_REG_WDT_TIMER2_EN_TIMER2_EN_MASK);

    // WDT_TIMER2_CTRL
    add_mask_entry(SOC_MCI_TOP_MCI_REG_WDT_TIMER2_CTRL,
                MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK);

    // WDT_STATUS
    add_mask_entry(SOC_MCI_TOP_MCI_REG_WDT_STATUS,
                MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK |
                MCI_REG_WDT_STATUS_T2_TIMEOUT_MASK); 

    // RESET_REQUEST
    add_mask_entry(SOC_MCI_TOP_MCI_REG_RESET_REQUEST,
                MCI_REG_RESET_REQUEST_MCU_REQ_MASK);

    // MCI_BOOTFSM_GO
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO,
                MCI_REG_MCI_BOOTFSM_GO_GO_MASK);

    // CPTRA_BOOT_GO
    add_mask_entry(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO,
                MCI_REG_CPTRA_BOOT_GO_GO_MASK);

    // FW_SRAM_EXEC_REGION_SIZE
    add_mask_entry(SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE,
                MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK); 

    // MBOX0_AXI_USER_LOCK_0
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0,
                MCI_REG_MBOX0_AXI_USER_LOCK_0_LOCK_MASK);

    // MBOX0_AXI_USER_LOCK_1
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_1,
                MCI_REG_MBOX0_AXI_USER_LOCK_1_LOCK_MASK);

    // MBOX0_AXI_USER_LOCK_2
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_2,
                MCI_REG_MBOX0_AXI_USER_LOCK_2_LOCK_MASK);

    // MBOX0_AXI_USER_LOCK_3
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_3,
                MCI_REG_MBOX0_AXI_USER_LOCK_3_LOCK_MASK);

    // MBOX0_AXI_USER_LOCK_4
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4,
                MCI_REG_MBOX0_AXI_USER_LOCK_4_LOCK_MASK);   

    // MBOX1_AXI_USER_LOCK_0
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_0,
                MCI_REG_MBOX1_AXI_USER_LOCK_0_LOCK_MASK);

    // MBOX1_AXI_USER_LOCK_1
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_1,
                MCI_REG_MBOX1_AXI_USER_LOCK_1_LOCK_MASK);

    // MBOX1_AXI_USER_LOCK_2
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_2,
                MCI_REG_MBOX1_AXI_USER_LOCK_2_LOCK_MASK);

    // MBOX1_AXI_USER_LOCK_3
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_3,
                MCI_REG_MBOX1_AXI_USER_LOCK_3_LOCK_MASK);

    // MBOX1_AXI_USER_LOCK_4
    add_mask_entry(SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_4,
                MCI_REG_MBOX1_AXI_USER_LOCK_4_LOCK_MASK); 

    // SS_DEBUG_INTENT
    add_mask_entry(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT,
                MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK);

    // SS_CONFIG_DONE_STICKY
    add_mask_entry(SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE_STICKY,
                MCI_REG_SS_CONFIG_DONE_STICKY_DONE_MASK);

    // SS_CONFIG_DONE
    add_mask_entry(SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE,
                MCI_REG_SS_CONFIG_DONE_DONE_MASK);   

    // INTR_BLOCK_RF_GLOBAL_INTR_EN_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,
                MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK);

    // INTR_BLOCK_RF_ERROR0_INTR_EN_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R,
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_INTERNAL_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX0_ECC_UNC_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_MBOX1_ECC_UNC_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK);

    // INTR_BLOCK_RF_ERROR1_INTR_EN_R (includes all 32 bits of AGG_ERROR_FATAL flags)
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R,
                0xFFFFFFFF); // All bits are used

    // INTR_BLOCK_RF_NOTIF0_INTR_EN_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R,
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MCU_SRAM_ECC_COR_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MCU_RESET_REQ_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_TARGET_DONE_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_TARGET_DONE_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_CMD_AVAIL_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_CMD_AVAIL_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_ECC_COR_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_ECC_COR_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_SCAN_MODE_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX0_SOC_REQ_LOCK_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_SOC_REQ_LOCK_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_OTP_OPERATION_DONE_EN_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_OTP_OPERATION_DONE_EN_MASK);

    // INTR_BLOCK_RF_NOTIF1_INTR_EN_R (includes all 32 bits of AGG_ERROR_NON_FATAL flags)
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R,
                0xFFFFFFFF); // All bits are used

    // ERROR_GLOBAL_INTR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS0_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS1_MASK);

    // NOTIF_GLOBAL_INTR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R,
                MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS0_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS1_MASK);

    // ERROR0_INTERNAL_INTR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX0_ECC_UNC_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_MBOX1_ECC_UNC_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK);

    // ERROR1_INTERNAL_INTR_R (includes all 32 bits of AGG_ERROR_FATAL status flags)
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R,
                0xFFFFFFFF); // All bits are used

    // NOTIF0_INTERNAL_INTR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R,
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MCU_SRAM_ECC_COR_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MCU_RESET_REQ_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_TARGET_DONE_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_TARGET_DONE_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_CMD_AVAIL_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_CMD_AVAIL_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_ECC_COR_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_ECC_COR_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX0_SOC_REQ_LOCK_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_SOC_REQ_LOCK_STS_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_OTP_OPERATION_DONE_STS_MASK);

    // NOTIF1_INTERNAL_INTR_R (includes all 32 bits of AGG_ERROR_NON_FATAL status flags)
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R,
                0xFFFFFFFF); // All bits are used

    // ERROR0_INTR_TRIG_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R,
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MCU_SRAM_DMI_AXI_COLLISION_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX0_ECC_UNC_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_MBOX1_ECC_UNC_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK);

    // ERROR1_INTR_TRIG_R (includes all 32 bits of AGG_ERROR_FATAL trigger flags)
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R,
                0xFFFFFFFF); // All bits are used

    // NOTIF0_INTR_TRIG_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R,
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MCU_SRAM_ECC_COR_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MCU_RESET_REQ_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_TARGET_DONE_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_TARGET_DONE_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_CMD_AVAIL_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_CMD_AVAIL_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_CPTRA_MBOX_CMD_AVAIL_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_ECC_COR_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_ECC_COR_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX0_SOC_REQ_LOCK_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_SOC_REQ_LOCK_TRIG_MASK |
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_OTP_OPERATION_DONE_TRIG_MASK);

    // NOTIF1_INTR_TRIG_R (includes all 32 bits of AGG_ERROR_NON_FATAL trigger flags)
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R,
                0xFFFFFFFF); // All bits are used   
    
    // ERROR_INTERNAL_INTR_COUNT_INCR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK);

    // ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK);

    // ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK);

    // ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK);

    // ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK);

    // ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R
    add_mask_entry(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R,
                MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_PULSE_MASK);

    // MCU_TRACE_BUFFER_CSR_STATUS
    add_mask_entry(SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS,
                MCU_TRACE_BUFFER_CSR_STATUS_WRAPPED_MASK |
                MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK);

    // MCU_MBOX0_CSR_MBOX_LOCK
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK,
                MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK);

    // MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID,
                MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID_VALID_MASK);

    // MCU_MBOX0_CSR_MBOX_EXECUTE
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE,
                MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    // MCU_MBOX0_CSR_MBOX_TARGET_STATUS
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS,
                MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_MASK |
                MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_MASK);

    // MCU_MBOX0_CSR_MBOX_CMD_STATUS
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS,
                MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK);

    // MCU_MBOX0_CSR_MBOX_HW_STATUS
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS,
                MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK |
                MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK);

    // MCU_MBOX1_CSR_MBOX_LOCK
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_LOCK,
                MCU_MBOX1_CSR_MBOX_LOCK_LOCK_MASK);

    // MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID,
                MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID_VALID_MASK);

    // MCU_MBOX1_CSR_MBOX_EXECUTE
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_EXECUTE,
                MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    // MCU_MBOX1_CSR_MBOX_TARGET_STATUS
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_STATUS,
                MCU_MBOX1_CSR_MBOX_TARGET_STATUS_STATUS_MASK |
                MCU_MBOX1_CSR_MBOX_TARGET_STATUS_DONE_MASK);

    // MCU_MBOX1_CSR_MBOX_CMD_STATUS
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD_STATUS,
                MCU_MBOX1_CSR_MBOX_CMD_STATUS_STATUS_MASK);

    // MCU_MBOX1_CSR_MBOX_HW_STATUS
    add_mask_entry(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_HW_STATUS,
                MCU_MBOX1_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK |
                MCU_MBOX1_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK);

    // MBOX_CSR_MBOX_LOCK
    add_mask_entry(SOC_MBOX_CSR_MBOX_LOCK,
                MBOX_CSR_MBOX_LOCK_LOCK_MASK);

    // MBOX_CSR_MBOX_EXECUTE
    add_mask_entry(SOC_MBOX_CSR_MBOX_EXECUTE,
                MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    // MBOX_CSR_MBOX_STATUS
    add_mask_entry(SOC_MBOX_CSR_MBOX_STATUS,
                MBOX_CSR_MBOX_STATUS_STATUS_MASK |
                MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_MASK |
                MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_MASK |
                MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK |
                MBOX_CSR_MBOX_STATUS_SOC_HAS_LOCK_MASK |
                MBOX_CSR_MBOX_STATUS_MBOX_RDPTR_MASK |
                MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_MASK);

    // MBOX_CSR_MBOX_UNLOCK
    add_mask_entry(SOC_MBOX_CSR_MBOX_UNLOCK,
                MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    // MBOX_CSR_TAP_MODE
    add_mask_entry(SOC_MBOX_CSR_TAP_MODE,
                MBOX_CSR_TAP_MODE_ENABLED_MASK);
}

/**
 * Add an entry to the register mask dictionary
 * 
 * @param address Register address
 * @param mask Combined mask for the register
 * @return 0 on success, -1 if dictionary is full
 */
int add_mask_entry(uint32_t address, uint32_t mask) {
    if (g_mask_dict.count < MAX_REGISTER_ENTRIES) {
        g_mask_dict.entries[g_mask_dict.count].address = address;
        g_mask_dict.entries[g_mask_dict.count].combined_mask = mask;
        g_mask_dict.count++;
        return 0;
    }
    return -1;
}

/**
 * Get the combined mask for a register
 * 
 * @param address Register address
 * @return Combined mask, or 0xFFFFFFFF if not found
 */
uint32_t get_register_mask(uint32_t address) {
    for (int i = 0; i < g_mask_dict.count; i++) {
        if (g_mask_dict.entries[i].address == address) {
            return g_mask_dict.entries[i].combined_mask;
        }
    }
    
    /* Default mask for unknown registers */
    return 0xFFFFFFFF;
}

/**
 * Initialize MCI module
 */
void mci_init(void) {
    // Initialize register mask dictionary if not already done

    VPRINTF(LOW, "Initializing mask dict and expected data dict\n");
    static int masks_initialized = 0;
    if (!masks_initialized) {
        init_mask_dict();
        masks_initialized = 1;
    }
    
    // Initialize expected data dictionary
    init_reg_exp_dict(&g_expected_data_dict);

    // Initialize excluded registers
    init_excluded_registers();
    
    // Perform other MCI initialization
    VPRINTF(LOW, "MCI module initialized\n");
    
}
