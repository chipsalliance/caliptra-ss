#ifndef MCI_REG_ACCESS_H
#define MCI_REG_ACCESS_H

#include <stdint.h>
#include "soc_address_map.h"
#include "riscv_hw_if.h"

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

/**
 * Read a specific field from an MCI register
 * 
 * @param reg_addr Register address
 * @param mask Bit mask for the field
 * @param shift Bit position (shift) for the field
 * @return The field value
 */
uint32_t mci_reg_read_field(uint32_t reg_addr, uint32_t mask, uint32_t shift) {
    uint32_t reg_val = mci_reg_read(reg_addr);
    return (reg_val & mask) >> shift;
}

/**
 * Update a specific field in an MCI register
 * 
 * @param reg_addr Register address
 * @param mask Bit mask for the field
 * @param shift Bit position (shift) for the field
 * @param field_val New value for the field
 */
void mci_reg_write_field(uint32_t reg_addr, uint32_t mask, uint32_t shift, uint32_t field_val) {
    uint32_t reg_val = mci_reg_read(reg_addr);
    
    // Clear the field bits
    reg_val &= ~mask;
    
    // Set the new field value
    reg_val |= ((field_val << shift) & mask);
    
    // Write the updated register value
    mci_reg_write(reg_addr, reg_val);
}

/**
 * Set specific bits in an MCI register
 * 
 * @param reg_addr Register address
 * @param mask Bit mask for the bits to set
 */
void mci_reg_set_bits(uint32_t reg_addr, uint32_t mask) {
    uint32_t reg_val = mci_reg_read(reg_addr);
    reg_val |= mask;
    mci_reg_write(reg_addr, reg_val);
}

/**
 * Clear specific bits in an MCI register
 * 
 * @param reg_addr Register address
 * @param mask Bit mask for the bits to clear
 */
void mci_reg_clear_bits(uint32_t reg_addr, uint32_t mask) {
    uint32_t reg_val = mci_reg_read(reg_addr);
    reg_val &= ~mask;
    mci_reg_write(reg_addr, reg_val);
}

/*
 * Helper functions for specific MCI registers
 */

/**
 * Read the MCI_REG_HW_REV_ID register
 * 
 * @return MCI generation value
 */
uint32_t mci_get_generation(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCI_REG_HW_REV_ID,
        MCI_REG_HW_REV_ID_MC_GENERATION_MASK,
        MCI_REG_HW_REV_ID_MC_GENERATION_LOW
    );
}

/**
 * Check if CAP_LOCK is locked
 * 
 * @return 1 if locked, 0 otherwise
 */
uint32_t mci_is_cap_locked(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCI_REG_CAP_LOCK,
        MCI_REG_CAP_LOCK_LOCK_MASK,
        MCI_REG_CAP_LOCK_LOCK_LOW
    );
}

/**
 * Lock the capability register
 */
void mci_lock_capabilities(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_CAP_LOCK,
        MCI_REG_CAP_LOCK_LOCK_MASK,
        MCI_REG_CAP_LOCK_LOCK_LOW,
        1
    );
}

/**
 * Read the MCI_REG_HW_CONFIG0 register
 * 
 * @param mbox0_size Pointer to store MBOX0 SRAM size
 * @param mbox1_size Pointer to store MBOX1 SRAM size
 */
void mci_get_mbox_sizes(uint32_t *mbox0_size, uint32_t *mbox1_size) {
    uint32_t config0 = mci_reg_read(SOC_MCI_TOP_MCI_REG_HW_CONFIG0);
    
    if (mbox0_size) {
        *mbox0_size = (config0 & MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_MASK) 
                       >> MCI_REG_HW_CONFIG0_MCU_MBOX0_SRAM_SIZE_LOW;
    }
    
    if (mbox1_size) {
        *mbox1_size = (config0 & MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_MASK) 
                       >> MCI_REG_HW_CONFIG0_MCU_MBOX1_SRAM_SIZE_LOW;
    }
}

/**
 * Read the MCI_REG_HW_CONFIG1 register
 * 
 * @return MCU SRAM size
 */
uint32_t mci_get_mcu_sram_size(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCI_REG_HW_CONFIG1,
        MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_MASK,
        MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_LOW
    );
}

/**
 * Read the boot FSM state
 * 
 * @return Boot FSM state
 */
uint32_t mci_get_boot_fsm_state(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS,
        MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK,
        MCI_REG_HW_FLOW_STATUS_BOOT_FSM_LOW
    );
}

/**
 * Read the reset reason
 * 
 * @return Reset reason flags
 */
uint32_t mci_get_reset_reason(void) {
    return mci_reg_read(SOC_MCI_TOP_MCI_REG_RESET_REASON);
}

/**
 * Check if the device is in debug locked state
 * 
 * @return 1 if debug is locked, 0 otherwise
 */
uint32_t mci_is_debug_locked(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCI_REG_SECURITY_STATE,
        MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK,
        MCI_REG_SECURITY_STATE_DEBUG_LOCKED_LOW
    );
}

/**
 * Get the device lifecycle state
 * 
 * @return Device lifecycle state
 */
uint32_t mci_get_device_lifecycle(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCI_REG_SECURITY_STATE,
        MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_MASK,
        MCI_REG_SECURITY_STATE_DEVICE_LIFECYCLE_LOW
    );
}

/**
 * Check if scan mode is enabled
 * 
 * @return 1 if scan mode is enabled, 0 otherwise
 */
uint32_t mci_is_scan_mode_enabled(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCI_REG_SECURITY_STATE,
        MCI_REG_SECURITY_STATE_SCAN_MODE_MASK,
        MCI_REG_SECURITY_STATE_SCAN_MODE_LOW
    );
}

/**
 * Check and get fatal hardware errors
 * 
 * @return Fatal error flags
 */
uint32_t mci_get_hw_error_fatal(void) {
    return mci_reg_read(SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL);
}

/**
 * Check and get non-fatal hardware errors
 * 
 * @return Non-fatal error flags
 */
uint32_t mci_get_hw_error_non_fatal(void) {
    return mci_reg_read(SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL);
}

/**
 * Enable Watchdog Timer 1
 */
void mci_enable_wdt1(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_WDT_TIMER1_EN,
        MCI_REG_WDT_TIMER1_EN_TIMER1_EN_MASK,
        MCI_REG_WDT_TIMER1_EN_TIMER1_EN_LOW,
        1
    );
}

/**
 * Disable Watchdog Timer 1
 */
void mci_disable_wdt1(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_WDT_TIMER1_EN,
        MCI_REG_WDT_TIMER1_EN_TIMER1_EN_MASK,
        MCI_REG_WDT_TIMER1_EN_TIMER1_EN_LOW,
        0
    );
}

/**
 * Restart Watchdog Timer 1
 */
void mci_restart_wdt1(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_WDT_TIMER1_CTRL,
        MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK,
        MCI_REG_WDT_TIMER1_CTRL_TIMER1_RESTART_LOW,
        1
    );
}

/**
 * Set timeout period for Watchdog Timer 1
 * 
 * @param timeout_low Lower 32 bits of timeout period
 * @param timeout_high Upper 32 bits of timeout period
 */
void mci_set_wdt1_timeout(uint32_t timeout_low, uint32_t timeout_high) {
    mci_reg_write(SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0, timeout_low);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1, timeout_high);
}

/**
 * Enable Watchdog Timer 2
 */
void mci_enable_wdt2(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN,
        MCI_REG_WDT_TIMER2_EN_TIMER2_EN_MASK,
        MCI_REG_WDT_TIMER2_EN_TIMER2_EN_LOW,
        1
    );
}

/**
 * Disable Watchdog Timer 2
 */
void mci_disable_wdt2(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN,
        MCI_REG_WDT_TIMER2_EN_TIMER2_EN_MASK,
        MCI_REG_WDT_TIMER2_EN_TIMER2_EN_LOW,
        0
    );
}

/**
 * Restart Watchdog Timer 2
 */
void mci_restart_wdt2(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_WDT_TIMER2_CTRL,
        MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK,
        MCI_REG_WDT_TIMER2_CTRL_TIMER2_RESTART_LOW,
        1
    );
}

/**
 * Set timeout period for Watchdog Timer 2
 * 
 * @param timeout_low Lower 32 bits of timeout period
 * @param timeout_high Upper 32 bits of timeout period
 */
void mci_set_wdt2_timeout(uint32_t timeout_low, uint32_t timeout_high) {
    mci_reg_write(SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0, timeout_low);
    mci_reg_write(SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1, timeout_high);
}

/**
 * Get the Watchdog Timer status
 * 
 * @param timer1_timeout Pointer to store Timer1 timeout status
 * @param timer2_timeout Pointer to store Timer2 timeout status
 */
void mci_get_wdt_status(uint32_t *timer1_timeout, uint32_t *timer2_timeout) {
    uint32_t status = mci_reg_read(SOC_MCI_TOP_MCI_REG_WDT_STATUS);
    
    if (timer1_timeout) {
        *timer1_timeout = (status & MCI_REG_WDT_STATUS_T1_TIMEOUT_MASK) 
                           >> MCI_REG_WDT_STATUS_T1_TIMEOUT_LOW;
    }
    
    if (timer2_timeout) {
        *timer2_timeout = (status & MCI_REG_WDT_STATUS_T2_TIMEOUT_MASK) 
                           >> MCI_REG_WDT_STATUS_T2_TIMEOUT_LOW;
    }
}

/**
 * Request MCU reset
 */
void mci_request_mcu_reset(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_RESET_REQUEST,
        MCI_REG_RESET_REQUEST_MCU_REQ_MASK,
        MCI_REG_RESET_REQUEST_MCU_REQ_LOW,
        1
    );
}

/**
 * Set MCU reset vector
 * 
 * @param reset_vector Reset vector address
 */
void mci_set_mcu_reset_vector(uint32_t reset_vector) {
    mci_reg_write(SOC_MCI_TOP_MCI_REG_MCU_RESET_VECTOR, reset_vector);
}

/**
 * Set MCU NMI vector
 * 
 * @param nmi_vector NMI vector address
 */
void mci_set_mcu_nmi_vector(uint32_t nmi_vector) {
    mci_reg_write(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, nmi_vector);
}

/**
 * Set SRAM execution region size
 * 
 * @param size SRAM execution region size
 */
void mci_set_sram_exec_region_size(uint32_t size) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE,
        MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK,
        MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_LOW,
        size
    );
}

/**
 * Lock MBOX0 to prevent changes
 */
void mci_lock_mbox0(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK,
        MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK,
        MCU_MBOX0_CSR_MBOX_LOCK_LOCK_LOW,
        1
    );
}

/**
 * Set MBOX0 command
 * 
 * @param cmd Command value
 */
void mci_set_mbox0_cmd(uint32_t cmd) {
    mci_reg_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD, cmd);
}

/**
 * Set MBOX0 data length
 * 
 * @param dlen Data length
 */
void mci_set_mbox0_dlen(uint32_t dlen) {
    mci_reg_write(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, dlen);
}

/**
 * Execute MBOX0 command
 */
void mci_execute_mbox0_cmd(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE,
        MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_MASK,
        MCU_MBOX0_CSR_MBOX_EXECUTE_EXECUTE_LOW,
        1
    );
}

/**
 * Get MBOX0 target status
 * 
 * @param status Pointer to store target status
 * @param done Pointer to store done status
 */
void mci_get_mbox0_target_status(uint32_t *status, uint32_t *done) {
    uint32_t target_status = mci_reg_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_STATUS);
    
    if (status) {
        *status = (target_status & MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_MASK) 
                   >> MCU_MBOX0_CSR_MBOX_TARGET_STATUS_STATUS_LOW;
    }
    
    if (done) {
        *done = (target_status & MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_MASK) 
                 >> MCU_MBOX0_CSR_MBOX_TARGET_STATUS_DONE_LOW;
    }
}

/**
 * Get MBOX0 command status
 * 
 * @return Command status
 */
uint32_t mci_get_mbox0_cmd_status(void) {
    return mci_reg_read_field(
        SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS,
        MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK,
        MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_LOW
    );
}

/**
 * Get MBOX0 hardware status
 * 
 * @param single_error Pointer to store ECC single error status
 * @param double_error Pointer to store ECC double error status
 */
void mci_get_mbox0_hw_status(uint32_t *single_error, uint32_t *double_error) {
    uint32_t hw_status = mci_reg_read(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS);
    
    if (single_error) {
        *single_error = (hw_status & MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK) 
                         >> MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_LOW;
    }
    
    if (double_error) {
        *double_error = (hw_status & MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK) 
                         >> MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_LOW;
    }
}

/* 
 * Similar functions for MBOX1 can be implemented following the same pattern as MBOX0 
 */

/**
 * Lock MBOX1 to prevent changes
 */
void mci_lock_mbox1(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_LOCK,
        MCU_MBOX1_CSR_MBOX_LOCK_LOCK_MASK,
        MCU_MBOX1_CSR_MBOX_LOCK_LOCK_LOW,
        1
    );
}

/**
 * Set MBOX1 command
 * 
 * @param cmd Command value
 */
void mci_set_mbox1_cmd(uint32_t cmd) {
    mci_reg_write(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_CMD, cmd);
}

/**
 * Set MBOX1 data length
 * 
 * @param dlen Data length
 */
void mci_set_mbox1_dlen(uint32_t dlen) {
    mci_reg_write(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_DLEN, dlen);
}

/**
 * Execute MBOX1 command
 */
void mci_execute_mbox1_cmd(void) {
    mci_reg_write_field(
        SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_EXECUTE,
        MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK,
        MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_LOW,
        1
    );
}

/**
 * Get MBOX1 target status
 * 
 * @param status Pointer to store target status
 * @param done Pointer to store done status
 */
void mci_get_mbox1_target_status(uint32_t *status, uint32_t *done) {
    uint32_t target_status = mci_reg_read(SOC_MCI_TOP_MCU_MBOX1_CSR_MBOX_TARGET_STATUS);
    
    if (status) {
        *status = (target_status & MCU_MBOX1_CSR_MBOX_TARGET_STATUS_STATUS_MASK) 
                   >> MCU_MBOX1_CSR_MBOX_TARGET_STATUS_STATUS_LOW;
    }
    
    if (done) {
        *done = (target_status & MCU_MBOX1_CSR_MBOX_TARGET_STATUS_DONE_MASK) 
                 >> MCU_MBOX1_CSR_MBOX_TARGET_STATUS_DONE_LOW;
    }
}

/* Interrupt-related functions */

/**
 * Enable global interrupts
 * 
 * @param error_en Enable error interrupts
 * @param notif_en Enable notification interrupts
 */
void mci_enable_global_interrupts(uint32_t error_en, uint32_t notif_en) {
    uint32_t val = 0;
    
    if (error_en) {
        val |= MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK;
    }
    
    if (notif_en) {
        val |= MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK;
    }
    
    mci_reg_write(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, val);
}

/**
 * Enable specific error interrupts
 * 
 * @param mask Bit mask for interrupts to enable
 */
void mci_enable_error0_interrupts(uint32_t mask) {
    mci_reg_set_bits(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R, mask);
}

/**
 * Enable specific notification interrupts
 * 
 * @param mask Bit mask for interrupts to enable
 */
void mci_enable_notif0_interrupts(uint32_t mask) {
    mci_reg_set_bits(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R, mask);
}

/**
 * Get error global interrupt status
 * 
 * @return Error global interrupt status
 */
uint32_t mci_get_error_global_intr_status(void) {
    return mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R);
}

/**
 * Get notification global interrupt status
 * 
 * @return Notification global interrupt status
 */
uint32_t mci_get_notif_global_intr_status(void) {
    return mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R);
}

/**
 * Get error0 internal interrupt status
 * 
 * @return Error0 internal interrupt status
 */
uint32_t mci_get_error0_internal_intr_status(void) {
    return mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R);
}

/**
 * Get notification0 internal interrupt status
 * 
 * @return Notification0 internal interrupt status
 */
uint32_t mci_get_notif0_internal_intr_status(void) {
    return mci_reg_read(SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
}

/* MCU Trace Buffer functions */

/**
 * Get trace buffer status
 * 
 * @param wrapped Pointer to store wrapped status
 * @param valid_data Pointer to store valid data status
 */
void mci_get_trace_buffer_status(uint32_t *wrapped, uint32_t *valid_data) {
    uint32_t status = mci_reg_read(SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_STATUS);
    
    if (wrapped) {
        *wrapped = (status & MCU_TRACE_BUFFER_CSR_STATUS_WRAPPED_MASK) 
                    >> MCU_TRACE_BUFFER_CSR_STATUS_WRAPPED_LOW;
    }
    
    if (valid_data) {
        *valid_data = (status & MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK) 
                       >> MCU_TRACE_BUFFER_CSR_STATUS_VALID_DATA_LOW;
    }
}

/**
 * Configure trace buffer
 * 
 * @param config Configuration value
 */
void mci_config_trace_buffer(uint32_t config) {
    mci_reg_write(SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_CONFIG, config);
}

/**
 * Read a data item from the trace buffer
 * 
 * @return Trace data
 */
uint32_t mci_read_trace_data(void) {
    return mci_reg_read(SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_DATA);
}

/**
 * Get trace buffer write pointer
 * 
 * @return Write pointer
 */
uint32_t mci_get_trace_write_ptr(void) {
    return mci_reg_read(SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_WRITE_PTR);
}

/**
 * Get trace buffer read pointer
 * 
 * @return Read pointer
 */
uint32_t mci_get_trace_read_ptr(void) {
    return mci_reg_read(SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR);
}

/**
 * Set trace buffer read pointer
 * 
 * @param ptr Read pointer value
 */
void mci_set_trace_read_ptr(uint32_t ptr) {
    mci_reg_write(SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_READ_PTR, ptr);
}

#endif /* MCI_REG_ACCESS_H */