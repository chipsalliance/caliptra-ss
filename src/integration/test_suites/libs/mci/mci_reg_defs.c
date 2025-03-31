#include <stddef.h>
#include "mci_reg_defs.h"
#include "mci_reg_access.h"  /* For register address definitions */

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
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_MBOX0 */
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
    
    /* REG_GROUP_MBOX1 */
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
    
    /* REG_GROUP_INTERRUPT */
    {
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, "GLOBAL_INTR_EN_R", "Global Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R, "ERROR0_INTR_EN_R", "Error 0 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R, "ERROR1_INTR_EN_R", "Error 1 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R, "NOTIF0_INTR_EN_R", "Notification 0 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R, "NOTIF1_INTR_EN_R", "Notification 1 Interrupt Enable" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R, "ERROR_GLOBAL_INTR_R", "Error Global Interrupt" },
        { SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R, "NOTIF_GLOBAL_INTR_R", "Notification Global Interrupt" },
        { 0, NULL, NULL }  /* End marker */
    },
    
    /* REG_GROUP_TRACE */
    {
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS, "TRACE_BUFFER_STATUS", "Trace Buffer Status" },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_CONFIG, "TRACE_BUFFER_CONFIG", "Trace Buffer Configuration" },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_DATA, "TRACE_BUFFER_DATA", "Trace Buffer Data" },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR, "TRACE_BUFFER_WRITE_PTR", "Trace Buffer Write Pointer" },
        { SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR, "TRACE_BUFFER_READ_PTR", "Trace Buffer Read Pointer" },
        { 0, NULL, NULL }  /* End marker */
    }
};

/* Function to get a string representation of a register group */
const char* get_group_name(mci_register_group_t group) {
    switch(group) {
        case REG_GROUP_CAPABILITIES: return "Capabilities";
        case REG_GROUP_HARDWARE_STATUS: return "Hardware Status";
        case REG_GROUP_ERROR: return "Error";
        case REG_GROUP_SECURITY: return "Security";
        case REG_GROUP_WATCHDOG: return "Watchdog";
        case REG_GROUP_MBOX0: return "Mailbox 0";
        case REG_GROUP_MBOX1: return "Mailbox 1";
        case REG_GROUP_INTERRUPT: return "Interrupt";
        case REG_GROUP_TRACE: return "Trace";
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