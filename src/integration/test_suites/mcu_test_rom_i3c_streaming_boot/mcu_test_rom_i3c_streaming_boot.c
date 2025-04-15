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

    //-- Boot MCU
    VPRINTF(LOW, "MCU: Booting... with fuses\n");
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

    for(uint8_t ii=0; ii<10000; ii++) {
        for (uint8_t ii = 0; ii < 16; ii++) {
            __asm__ volatile ("nop");
        }    
    }

    SEND_STDOUT_CTRL(0xff);
}