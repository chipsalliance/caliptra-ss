// Description: I3C Smoke test for Caliptra Subsystem
// Author     : Nilesh Patel
// Created    : 2025-01-14
// Comments   : 
//  This is a smoke test for I3C interface on Caliptra. 
//  The test brings up the I3C interface and sends a command to the I3C device. 
//  The test is expected to pass if the I3C device responds with the expected data.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "string.h"
#include "stdint.h"

#define STATUS_CHECK_LOOP_COUNT_FOR_RECOVERY 20

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
// volatile char* stdout = (char *)0xd0580000;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main (void) {

    int argc=0;
    char *argv[1];
    uint32_t i3c_reg_data;

    //-- Boot MCU
    VPRINTF(LOW, "MCU: Booting... \n");
    boot_mcu();

    // -- Boot I3C Core
    VPRINTF(LOW, "MCU: Boot I3C Core\n");
    boot_i3c_core();  

    //setting device address to 0x5A
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 90 << 0  | i3c_reg_data;
    i3c_reg_data = 1  << 15 | i3c_reg_data;
    lsu_write_32( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_DEVICE_ADDR, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C Device Address set to 0x5A\n");

    //setting virtual device address to 0x5B
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 91 << 0  | i3c_reg_data; //0x5B
    i3c_reg_data = 1  << 15 | i3c_reg_data;   
    lsu_write_32 ( SOC_I3CCSR_I3C_EC_STDBYCTRLMODE_STBY_CR_VIRT_DEVICE_ADDR, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C Virtual Device Address set to 0x5B\n");

    VPRINTF(LOW, "MCU: Updating I3C Recovery Registers\n");
    // Programming I3C for Recovery Mode 
    // - DEVICE_STATUS_0
    i3c_reg_data = 0x00000003; // Recovery mode - ready to accept recovery image
    i3c_reg_data = 1 << 12 | i3c_reg_data; // Flashless/Streaming Boot (FSB) (Reason of recovery) 
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, i3c_reg_data);

    // - RECOVERY_STATU_0
    i3c_reg_data = 0x00000001; // Awaiting recovery image
    lsu_write_32( SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C Recovery Registers updated\n");

    //-- Read INDIRTECT_FIFO_CTRL Register for non-zero value
    i3c_reg_data = 0x00000000;
    
    while(1) {

        i3c_reg_data = 0x00000000;
        i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1);
        VPRINTF(LOW, "MCU: Read INDIRECT_FIFO_CTRL_1 with 'h %0x\n", i3c_reg_data);
        if (i3c_reg_data != 0x00000000) {
            break;
        }
        for (uint8_t ii = 0; ii < 100; ii++) {
            __asm__ volatile ("nop");    
        }    
    }

    VPRINTF(LOW, "MCU: INDIRECT_FIFO_CTRL_1 is not zero\n");   
    VPRINTF(LOW, "MCU: End of I3C Reg Read Write Test\n");
    SEND_STDOUT_CTRL(0xff);
}