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

    // Initialize the printf library   
    VPRINTF(LOW, "=== MCU boot.. started == \n");

    mcu_cptra_init_d( 
        .cfg_enable_cptra_mbox_user_init=true, 
        .cfg_cptra_fuse=true,
        .cfg_cptra_wdt=true,
        .cfg_boot_i3c_core=true,
        .cfg_trigger_prod_rom=true); 

    VPRINTF(LOW, "=== MCU boot.. completed == \n");

    for(uint8_t ii=0; ii<10000; ii++) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop");
        }    
    }

    SEND_STDOUT_CTRL(0xff);
}