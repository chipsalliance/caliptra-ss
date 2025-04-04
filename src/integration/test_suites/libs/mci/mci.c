/**
 * @file mci.c
 * @brief Consolidated MCI library implementation
 */

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "mci.h"
#include "riscv_hw_if.h"
#include "caliptra_ss_lib.h"
#include "printf.h"

#define ADDRESS_BITS_FOR_INDEXING 12   // Using 12 bits gives us 4096 possible indices
#define BITMAP_SIZE_WORDS ((1 << ADDRESS_BITS_FOR_INDEXING) / 32)

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

/* Array of register infos by group */
const mci_register_info_t register_groups[][MAX_REGISTERS_PER_GROUP] = {
    /* REG_GROUP_CAPABILITIES */
    {
        { SOC_MCI_TOP_MCI_REG_HW_CAPABILITIES, "HW_CAPABILITIES", "Hardware Capabilities" },
        { SOC_MCI_TOP_MCI_REG_FW_CAPABILITIES, "FW_CAPABILITIES", "Firmware Capabilities" },
        { SOC_MCI_TOP_MCI_REG_CAP_LOCK, "CAP_LOCK", "Capability Lock" },
        { SOC_MCI_TOP_MCI_REG_HW_REV_ID, "HW_REV_ID", "Hardware Revision ID" },
        { SOC_MCI_TOP_MCI_REG_FW_REV_ID_0, "FW_REV_ID_0", "Firmware Revision ID 0" },
        { SOC_MCI_TOP_MCI_REG_FW_REV_ID_1, "FW_REV_ID_1", "Firmware Revision ID 1" },
        { SOC_MCI_TOP_MCI_REG_HW_CONFIG0, "HW_CONFIG0", "Hardware Configuration 0" },
        { SOC_MCI_TOP_MCI_REG_HW_CONFIG1, "HW_CONFIG1", "Hardware Configuration 1" },
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_HARDWARE_STATUS */
    {
        { SOC_MCI_TOP_MCI_REG_FW_FLOW_STATUS, "FW_FLOW_STATUS", "Firmware Flow Status" },
        { SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS, "HW_FLOW_STATUS", "Hardware Flow Status" },
        { SOC_MCI_TOP_MCI_REG_RESET_REASON, "RESET_REASON", "Reset Reason" },
        { SOC_MCI_TOP_MCI_REG_RESET_STATUS, "RESET_STATUS", "Reset Status" },
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_ERROR */
    {
        { SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", "Hardware Fatal Error" },
        { SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL, "AGG_ERROR_FATAL", "Aggregated Fatal Error" },
        { SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL, "HW_ERROR_NON_FATAL", "Hardware Non-Fatal Error" },
        { SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL, "AGG_ERROR_NON_FATAL", "Aggregated Non-Fatal Error" },
        { SOC_MCI_TOP_MCI_REG_FW_ERROR_FATAL, "FW_ERROR_FATAL", "Firmware Fatal Error" },
        { SOC_MCI_TOP_MCI_REG_FW_ERROR_NON_FATAL, "FW_ERROR_NON_FATAL", "Firmware Non-Fatal Error" },
        { SOC_MCI_TOP_MCI_REG_HW_ERROR_ENC, "HW_ERROR_ENC", "Hardware Error Enc"},
        { SOC_MCI_TOP_MCI_REG_FW_ERROR_ENC, "FW_ERROR_ENC", "Firmware Error Enc"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_0, "FW_EXTENDED_ERROR_INFO_0", "Firmware Extended Error Info 0"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_1, "FW_EXTENDED_ERROR_INFO_1", "Firmware Extended Error Info 1"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_2, "FW_EXTENDED_ERROR_INFO_2", "Firmware Extended Error Info 2"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_3, "FW_EXTENDED_ERROR_INFO_3", "Firmware Extended Error Info 3"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_4, "FW_EXTENDED_ERROR_INFO_4", "Firmware Extended Error Info 4"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_5, "FW_EXTENDED_ERROR_INFO_5", "Firmware Extended Error Info 5"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_6, "FW_EXTENDED_ERROR_INFO_6", "Firmware Extended Error Info 6"},
        { SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_7, "FW_EXTENDED_ERROR_INFO_7", "Firmware Extended Error Info 7"},
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_SECURITY */
    {
        { SOC_MCI_TOP_MCI_REG_SECURITY_STATE, "SECURITY_STATE", "Security State" },
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_WATCHDOG */
    {
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_EN, "WDT_TIMER1_EN", "Watchdog Timer 1 Enable" },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_CTRL, "WDT_TIMER1_CTRL", "Watchdog Timer 1 Control" },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0, "WDT_TIMER1_TIMEOUT_PERIOD_0", "Watchdog Timer 1 Timeout Period 0" },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1, "WDT_TIMER1_TIMEOUT_PERIOD_1", "Watchdog Timer 1 Timeout Period 1" },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN, "WDT_TIMER2_EN", "Watchdog Timer 2 Enable" },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_CTRL, "WDT_TIMER2_CTRL", "Watchdog Timer 2 Control" },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0, "WDT_TIMER2_TIMEOUT_PERIOD_0", "Watchdog Timer 2 Timeout Period 0" },
        { SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1, "WDT_TIMER2_TIMEOUT_PERIOD_1", "Watchdog Timer 2 Timeout Period 1" },
        { SOC_MCI_TOP_MCI_REG_WDT_STATUS, "WDT_STATUS", "Watchdog Status" },
        { SOC_MCI_TOP_MCI_REG_WDT_CFG_0, "WDT_CFG_0", "Watchdog Timer 0 Config" },
        { SOC_MCI_TOP_MCI_REG_WDT_CFG_1, "WDT_CFG_1", "Watchdog Timer 1 Config" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_MCU */
    {
        { SOC_MCI_TOP_MCI_REG_MCU_TIMER_CONFIG, "MCU_TIMER_CONFIG", "MCU Timer Config" },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L, "MCU_RV_MTIME_L", "MCU RiscV MTime Low" },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H, "MCU_RV_MTIME_H", "MCU RiscV MTime High" },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_L, "MCU_RV_MTIMECMP_L", "MCU RiscV MTimeCmp Low" },
        { SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_H, "MCU_RV_MTIMECMP_H", "MCU RiscV MTimeCmp High" }, 
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_CONTROL */
    {
        { SOC_MCI_TOP_MCI_REG_RESET_REQUEST, "RESET_REQUEST", "Reset Request" },
        { SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO, "MCI_BOOTFSM_GO", "MCI BootFSM Go" },
        { SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, "CPTRA_BOOT_GO", "Caliptra Boot Go" },
        { SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE, "FW_SRAM_EXEC_REGION_SIZE", "Firmware SRAM Execution Size" },
        { SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, "MCU_NMI_VECTOR", "MCI Non Maskable Interrupt Vector" }, 
        { SOC_MCI_TOP_MCI_REG_MCU_RESET_VECTOR, "MCU_RESET_VECTOR", "MCI Reset Vector" }, 
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_MCI_MBOX0 */
    {
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0, "MBOX0_VALID_AXI_USER_0", "Mailbox 0 Valid AXI User 0" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_1, "MBOX0_VALID_AXI_USER_1", "Mailbox 0 Valid AXI User 1" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_2, "MBOX0_VALID_AXI_USER_2", "Mailbox 0 Valid AXI User 2" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_3, "MBOX0_VALID_AXI_USER_3", "Mailbox 0 Valid AXI User 3" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4, "MBOX0_VALID_AXI_USER_4", "Mailbox 0 Valid AXI User 4" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0, "MBOX0_AXI_USER_LOCK_0", "Mailbox 0 Valid AXI Lock 0" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_1, "MBOX0_AXI_USER_LOCK_1", "Mailbox 0 Valid AXI Lock 1" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_2, "MBOX0_AXI_USER_LOCK_2", "Mailbox 0 Valid AXI Lock 2" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_3, "MBOX0_AXI_USER_LOCK_3", "Mailbox 0 Valid AXI Lock 3" },
        { SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4, "MBOX0_AXI_USER_LOCK_4", "Mailbox 0 Valid AXI Lock 4" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_MCU_MBOX0 */
    {
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK, "MBOX0_LOCK", "Mailbox 0 Lock" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER, "MBOX0_USER", "Mailbox 0 User" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER, "MBOX0_TARGET_USER", "Mailbox 0 Target User" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID, "MBOX0_TARGET_USER_VALID", "Mailbox 0 Target User Valid" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD, "MBOX0_CMD", "Mailbox 0 Command" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, "MBOX0_DLEN", "Mailbox 0 Data Length" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, "MBOX0_EXECUTE", "Mailbox 0 Execute" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS, "MBOX0_TARGET_STATUS", "Mailbox 0 Target Status" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS, "MBOX0_CMD_STATUS", "Mailbox 0 Command Status" },
        { SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS, "MBOX0_HW_STATUS", "Mailbox 0 Hardware Status" },
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_MCI_MBOX1 */
    {
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_0, "MBOX1_VALID_AXI_USER_0", "Mailbox 1 Valid AXI User 0" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_1, "MBOX1_VALID_AXI_USER_1", "Mailbox 1 Valid AXI User 1" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_2, "MBOX1_VALID_AXI_USER_2", "Mailbox 1 Valid AXI User 2" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_3, "MBOX1_VALID_AXI_USER_3", "Mailbox 1 Valid AXI User 3" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_4, "MBOX1_VALID_AXI_USER_4", "Mailbox 1 Valid AXI User 4" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_0, "MBOX1_AXI_USER_LOCK_0", "Mailbox 1 Valid AXI Lock 0" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_1, "MBOX1_AXI_USER_LOCK_1", "Mailbox 1 Valid AXI Lock 1" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_2, "MBOX1_AXI_USER_LOCK_2", "Mailbox 1 Valid AXI Lock 2" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_3, "MBOX1_AXI_USER_LOCK_3", "Mailbox 1 Valid AXI Lock 3" },
        { SOC_MCI_TOP_MCI_REG_MBOX1_AXI_USER_LOCK_4, "MBOX1_AXI_USER_LOCK_4", "Mailbox 1 Valid AXI Lock 4" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_MCU_MBOX1 */
    {
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_LOCK, "MBOX1_LOCK", "Mailbox 1 Lock" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_USER, "MBOX1_USER", "Mailbox 1 User" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_USER, "MBOX1_TARGET_USER", "Mailbox 1 Target User" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_USER_VALID, "MBOX1_TARGET_USER_VALID", "Mailbox 1 Target User Valid" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD, "MBOX1_CMD", "Mailbox 1 Command" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_DLEN, "MBOX1_DLEN", "Mailbox 1 Data Length" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_EXECUTE, "MBOX1_EXECUTE", "Mailbox 1 Execute" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_STATUS, "MBOX1_TARGET_STATUS", "Mailbox 1 Target Status" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD_STATUS, "MBOX1_CMD_STATUS", "Mailbox 1 Command Status" },
        { SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_HW_STATUS, "MBOX1_HW_STATUS", "Mailbox 1 Hardware Status" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DFT */
    {
        { SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_0, "SOC_DFT_EN_0", "SoC DFT Enable 0" },
        { SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_1, "SOC_DFT_EN_1", "SoC DFT Enable 1" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DEBUG */
    {
        { SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_0, "HW_DEBUG_EN_0", "Hardware Debug Enable 0" },
        { SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_1, "HW_DEBUG_EN_1", "Hardware Debug Enable 1" },
        { SOC_MCI_TOP_MCI_REG_SOC_PROD_DEBUG_STATE_0, "PROD_DEBUG_STATE_0", "Production Debug State 0" },
        { SOC_MCI_TOP_MCI_REG_SOC_PROD_DEBUG_STATE_1, "PROD_DEBUG_STATE_1", "Production Debug State 1" },
        { SOC_MCI_TOP_MCI_REG_FC_FIPS_ZEROZATION, "FC_FIPS_ZEROZATION", "Fuse Controller FIPS Zeroization" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_GENERIC_WIRES */
    { 
        { SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0, "GENERIC_INPUT_WIRES_0", "Generic Input Wires 0" },
        { SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1, "GENERIC_INPUT_WIRES_1", "Generic Input Wires 1" },
        { SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0, "GENERIC_OUTPUT_WIRES_0", "Generic Output Wires 0" },
        { SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1, "GENERIC_OUTPUT_WIRES_1", "Generic Output Wires 1" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_SS */
    { 
        { SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT, "SS_DEBUG_INTENT", "Subsystem Debug Intent" },
        { SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE_STICKY, "SS_DCONFIG_DONE_STICKY", "Subsystem Config done sticky" },
        { SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE, "SS_CONFIG_DONE", "Subsystem Config Done" },
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_0 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0", "Debug Unlock PK Hash 0_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1", "Debug Unlock PK Hash 0_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2", "Debug Unlock PK Hash 0_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3", "Debug Unlock PK Hash 0_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4", "Debug Unlock PK Hash 0_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5", "Debug Unlock PK Hash 0_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6", "Debug Unlock PK Hash 0_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7", "Debug Unlock PK Hash 0_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8", "Debug Unlock PK Hash 0_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9", "Debug Unlock PK Hash 0_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10", "Debug Unlock PK Hash 0_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11", "Debug Unlock PK Hash 0_11" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_1 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0", "Debug Unlock PK Hash 1_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1", "Debug Unlock PK Hash 1_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2", "Debug Unlock PK Hash 1_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3", "Debug Unlock PK Hash 1_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4", "Debug Unlock PK Hash 1_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5", "Debug Unlock PK Hash 1_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6", "Debug Unlock PK Hash 1_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7", "Debug Unlock PK Hash 1_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8", "Debug Unlock PK Hash 1_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9", "Debug Unlock PK Hash 1_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10", "Debug Unlock PK Hash 1_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11", "Debug Unlock PK Hash 1_11" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_2 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0", "Debug Unlock PK Hash 2_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1", "Debug Unlock PK Hash 2_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2", "Debug Unlock PK Hash 2_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3", "Debug Unlock PK Hash 2_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4", "Debug Unlock PK Hash 2_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5", "Debug Unlock PK Hash 2_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6", "Debug Unlock PK Hash 2_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7", "Debug Unlock PK Hash 2_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8", "Debug Unlock PK Hash 2_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9", "Debug Unlock PK Hash 2_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10", "Debug Unlock PK Hash 2_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11", "Debug Unlock PK Hash 2_11" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_3 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0", "Debug Unlock PK Hash 3_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1", "Debug Unlock PK Hash 3_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2", "Debug Unlock PK Hash 3_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3", "Debug Unlock PK Hash 3_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4", "Debug Unlock PK Hash 3_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5", "Debug Unlock PK Hash 3_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6", "Debug Unlock PK Hash 3_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7", "Debug Unlock PK Hash 3_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8", "Debug Unlock PK Hash 3_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9", "Debug Unlock PK Hash 3_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10", "Debug Unlock PK Hash 3_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11", "Debug Unlock PK Hash 3_11" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_4 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0", "Debug Unlock PK Hash 4_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1", "Debug Unlock PK Hash 4_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2", "Debug Unlock PK Hash 4_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3", "Debug Unlock PK Hash 4_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4", "Debug Unlock PK Hash 4_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5", "Debug Unlock PK Hash 4_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6", "Debug Unlock PK Hash 4_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7", "Debug Unlock PK Hash 4_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8", "Debug Unlock PK Hash 4_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9", "Debug Unlock PK Hash 4_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10", "Debug Unlock PK Hash 4_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11", "Debug Unlock PK Hash 4_11" },
        { 0, NULL, NULL }  /* End marker */
      },

    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_5 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0", "Debug Unlock PK Hash 5_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1", "Debug Unlock PK Hash 5_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2", "Debug Unlock PK Hash 5_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3", "Debug Unlock PK Hash 5_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4", "Debug Unlock PK Hash 5_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5", "Debug Unlock PK Hash 5_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6", "Debug Unlock PK Hash 5_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7", "Debug Unlock PK Hash 5_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8", "Debug Unlock PK Hash 5_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9", "Debug Unlock PK Hash 5_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10", "Debug Unlock PK Hash 5_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11", "Debug Unlock PK Hash 5_11" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_6 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0", "Debug Unlock PK Hash 6_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1", "Debug Unlock PK Hash 6_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2", "Debug Unlock PK Hash 6_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3", "Debug Unlock PK Hash 6_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4", "Debug Unlock PK Hash 6_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5", "Debug Unlock PK Hash 6_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6", "Debug Unlock PK Hash 6_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7", "Debug Unlock PK Hash 6_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8", "Debug Unlock PK Hash 6_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9", "Debug Unlock PK Hash 6_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10", "Debug Unlock PK Hash 6_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11", "Debug Unlock PK Hash 6_11" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_DEBUG_UNLOCK_PK_HASH_7 */
    {
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0", "Debug Unlock PK Hash 7_0" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1", "Debug Unlock PK Hash 7_1" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2", "Debug Unlock PK Hash 7_2" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3", "Debug Unlock PK Hash 7_3" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4", "Debug Unlock PK Hash 7_4" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5", "Debug Unlock PK Hash 7_5" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6", "Debug Unlock PK Hash 7_6" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7", "Debug Unlock PK Hash 7_7" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8", "Debug Unlock PK Hash 7_8" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9", "Debug Unlock PK Hash 7_9" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10", "Debug Unlock PK Hash 7_10" },
        { SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11, "PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11", "Debug Unlock PK Hash 7_11" },
        { 0, NULL, NULL }  /* End marker */
    },
        
    /* REG_GROUP_INTERRUPT */
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, "GLOBAL_INTR_EN_R", "Global Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R, "ERROR0_INTR_EN_R", "Error 0 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R, "ERROR1_INTR_EN_R", "Error 1 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R, "NOTIF0_INTR_EN_R", "Notification 0 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R, "NOTIF1_INTR_EN_R", "Notification 1 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R, "ERROR_GLOBAL_INTR_R", "Error Global Interrupt" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R, "NOTIF_GLOBAL_INTR_R", "Notification Global Interrupt" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R, "ERROR0_INTERNAL_INTR_R", "Error 0 Internal Interrupt" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R, "ERROR1_INTERNAL_INTR_R", "Error 1 Internal Interrupt" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R, "NOTIF0_INTERNAL_INTR_R", "Notification 0 Internal Interrupt" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R, "NOTIF1_INTERNAL_INTR_R", "Notification 1 Internal Interrupt" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R, "ERROR0_INTR_TRIG_R", "Error 0 Internal Trigger" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R, "ERROR1_INTR_TRIG_R", "Error 1 Internal Trigger" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R, "NOTIF0_INTR_TRIG_R", "Notification 0 Internal Trigger" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R, "NOTIF1_INTR_TRIG_R", "Notification 1 Internal Trigger" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_INTERRUPT_COUNTERS */
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R, "ERROR_INTERNAL_INTR_COUNT_R", "Error Internal Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R, "ERROR_MBOX0_ECC_UNC_INTR_COUNT_R", "Error MBOX0 ECC Uncorrectable Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R, "ERROR_MBOX1_ECC_UNC_INTR_COUNT_R", "Error MBOX1 ECC Uncorrectable Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R, "ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R", "Error MCU SRAM DMI AXI Collision Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R, "ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R", "Error WDT Timer1 Timeout Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R, "ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R", "Error WDT Timer2 Timeout Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R, "NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R", "Notification MCU SRAM ECC Correctable Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R, "NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R", "Notification CPTRA MCU Reset Request Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R, "NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R", "Notification General Input Toggle Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R, "NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R", "Notification MBOX0 Target Done Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R, "NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R", "Notification MBOX1 Target Done Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R, "NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R", "Notification MBOX0 Command Available Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R, "NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R", "Notification MBOX1 Command Available Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R, "NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R", "Notification CPTRA MBOX Command Available Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R, "NOTIF_MBOX0_ECC_COR_INTR_COUNT_R", "Notification MBOX0 ECC Correctable Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R, "NOTIF_MBOX1_ECC_COR_INTR_COUNT_R", "Notification MBOX1 ECC Correctable Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R, "NOTIF_DEBUG_LOCKED_INTR_COUNT_R", "Notification Debug Locked Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R, "NOTIF_SCAN_MODE_INTR_COUNT_R", "Notification Scan Mode Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R, "NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R", "Notification MBOX0 SOC Request Lock Interrupt Count" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R, "NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R", "Notification MBOX1 SOC Request Lock Interrupt Count" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_TRACE */
    {
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, "MCU_TRACE_BUFFER_CSR_STATUS", "Trace Buffer Status" },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_CONFIG, "MCU_TRACE_BUFFER_CSR_CONFIG", "Trace Buffer Configuration" },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_DATA, "MCU_TRACE_BUFFER_CSR_DATA", "Trace Buffer Data" },
        //{ SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR, "MCU_TRACE_BUFFER_CSR_WRITE_PTR", "Trace Buffer Write Pointer" },
        //{ SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR, "MCU_TRACE_BUFFER_CSR_READ_PTR", "Trace Buffer Read Pointer" },
        { 0, NULL, NULL }  /* End marker */
    },

    /* REG_GROUP_SOC_MBOX_CSR */
    {
        { SOC_MBOX_CSR_MBOX_LOCK, "MBOX_LOCK", "Mailbox Lock" },
        { SOC_MBOX_CSR_MBOX_USER, "MBOX_USER", "Mailbox User" },
        { SOC_MBOX_CSR_MBOX_CMD, "MBOX_CMD", "Mailbox Command" },
        { SOC_MBOX_CSR_MBOX_DLEN, "MBOX_DLEN", "Mailbox Data Length" },
        { SOC_MBOX_CSR_MBOX_DATAIN, "MBOX_DATAIN", "Mailbox Data Input" },
        { SOC_MBOX_CSR_MBOX_DATAOUT, "MBOX_DATAOUT", "Mailbox Data Output" },
        { SOC_MBOX_CSR_MBOX_EXECUTE, "MBOX_EXECUTE", "Mailbox Execute" },
        { SOC_MBOX_CSR_MBOX_STATUS, "MBOX_STATUS", "Mailbox Status" },
        { SOC_MBOX_CSR_MBOX_UNLOCK, "MBOX_UNLOCK", "Mailbox Unlock" },
        { SOC_MBOX_CSR_TAP_MODE, "TAP_MODE", "TAP Mode" },
        { 0, NULL, NULL }  /* End marker */
    }
};

/* Function to get a string representation of a register group */
const char* get_group_name(mci_register_group_t group) {
    switch(group) {
        case REG_GROUP_CAPABILITIES: return "Capabilities";
        case REG_GROUP_HARDWARE_STATUS: return "Hardware Status";
        case REG_GROUP_ERROR: return "Fatal/Non-Fatal Error";
        case REG_GROUP_SECURITY: return "Security";
        case REG_GROUP_WATCHDOG: return "Watchdog";
        case REG_GROUP_MCU: return "MCU";
        case REG_GROUP_CONTROL: return "Control";
        case REG_GROUP_MCI_MBOX0: return "MCI Mailbox 0";
        case REG_GROUP_MCU_MBOX0: return "MCU Mailbox 0";
        case REG_GROUP_MCI_MBOX1: return "MCI Mailbox 1";
        case REG_GROUP_MCU_MBOX1: return "MCU Mailbox 1";
        case REG_GROUP_DFT: return "DFT";
        case REG_GROUP_DEBUG: return "Debug";
        case REG_GROUP_GENERIC_WIRES: return "Generic Wires";
        case REG_GROUP_SS: return "Subsystem";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_0: return "Debug Unlock PK Hash 0";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_1: return "Debug Unlock PK Hash 1";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_2: return "Debug Unlock PK Hash 2";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_3: return "Debug Unlock PK Hash 3";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_4: return "Debug Unlock PK Hash 4";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_5: return "Debug Unlock PK Hash 5";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_6: return "Debug Unlock PK Hash 6";
        case REG_GROUP_DEBUG_UNLOCK_PK_HASH_7: return "Debug Unlock PK Hash 7";
        case REG_GROUP_INTERRUPT: return "Interrupt";
        case REG_GROUP_INTERRUPT_COUNTERS: return "Interrupt Counters";
        case REG_GROUP_TRACE: return "Trace";
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
    dict->count = 0;
}

/**
 * Add or update an entry in the register expected data dictionary
 * 
 * @param dict Pointer to dictionary
 * @param address Register address (key)
 * @param name Register name
 * @param value Expected data value
 * @return 0 on success, -1 if dictionary is full
 */
int set_reg_exp_data(mci_reg_exp_dict_t *dict, uint32_t address, const char *name, uint32_t value, uint32_t mask) {
    // First check if entry already exists
    for (int i = 0; i < dict->count; i++) {
        if (dict->entries[i].address == address) {
            // Update existing entry
            dict->entries[i].expected_data = value & mask;
            return 0;
        }
    }
    
    // Add new entry if space available
    if (dict->count < MAX_REGISTER_ENTRIES) {
        dict->entries[dict->count].address = address;
        dict->entries[dict->count].expected_data = value & mask;
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
    printf("Writing random values to all %s registers (%d total):\n", get_group_name(group), count);
    
    for (int i = 0; i < count; i++) {
        const mci_register_info_t *reg = get_register_info(group, i);
        
        if (reg) {
            // Check if this register should be excluded using our efficient method
            if (!is_register_excluded(reg->address)) {
                // Generate a unique value for each register
                uint32_t rand_value = xorshift32() & i;
            
                VPRINTF(MEDIUM, "  Writing 0x%08x to %s (0x%08x)\n", rand_value, reg->name, reg->address);
                mci_reg_write(reg->address, rand_value);
                
                /* Get mask for this register */
                uint32_t mask = get_register_mask(reg->address);
                
                // Store in dictionary
                if (set_reg_exp_data(dict, reg->address, reg->name, rand_value, mask) != 0) {
                    printf("  WARNING: Could not store expected data for %s\n", reg->name);
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
int read_register_group_and_verify(mci_register_group_t group, mci_reg_exp_dict_t *dict) {
    uint32_t read_data;
    int count = get_register_count(group);
    int mismatch_count = 0;
    
    printf("Reading and verifying %s registers (%d total):\n", get_group_name(group), count);
    
    for (int i = 0; i < count; i++) {
        const mci_register_info_t *reg = get_register_info(group, i);
        
        if (reg) {
            // Skip excluded registers with our efficient collision-aware check
            if (is_register_excluded(reg->address)) {
                VPRINTF(MEDIUM, "  Skipping excluded register %s (0x%08x)\n", reg->name, reg->address);
                continue;
            }
            
            // Read the register value
            read_data = mci_reg_read(reg->address);
            
            // Get expected data from dictionary
            uint32_t exp_data;
            if (get_reg_exp_data(dict, reg->address, &exp_data) == 0) {
                // Compare and report
                if (read_data == exp_data) {
                    VPRINTF(MEDIUM,"  Match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                           reg->name, reg->address, read_data, exp_data);
                } else {
                    printf("  No match: %s (0x%08x): Read 0x%08x, Expected 0x%08x\n", 
                           reg->name, reg->address, read_data, exp_data);
                    mismatch_count++;
                }
            } else {
                printf("  ! %s (0x%08x): Read 0x%08x, No expected data in dictionary\n", 
                       reg->name, reg->address, read_data);
            }
        } else {
            printf("  ! Register index %d not found in group\n", i);
        }
    }
    
    printf("Verification complete: %d register(s) matched, %d register(s) mismatched\n", 
           count - mismatch_count, mismatch_count);
    
    return mismatch_count;
}



void init_mask_dict(void) {
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
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_NOTIF_MBOX1_SOC_REQ_LOCK_EN_MASK);

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
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_NOTIF_MBOX1_SOC_REQ_LOCK_STS_MASK);

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
                MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_NOTIF_MBOX1_SOC_REQ_LOCK_TRIG_MASK);

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
    printf("MCI module initialized\n");
    
}