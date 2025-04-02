

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

    //-- Enable I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE 
    i3c_reg_data = 0xFFFFFFFF;
    lsu_write_32(SOC_I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE, i3c_reg_data);
    VPRINTF(LOW, "MCU: I3C TTI Interrupt Enable set to 0xFFFFFFFF\n");
    // read I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE
    i3c_reg_data = 0x00000000;
    i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_INTERRUPT_ENABLE);
    VPRINTF(LOW, "MCU: I3C TTI Interrupt Enable is 'h %0x\n", i3c_reg_data);

    // // -- read data from DCCM
    // VPRINTF(LOW, "MCU: Reading data from DCCM\n");
    // uint32_t dccm_data;
    // for (uint32_t ii = 0; ii < 4; ii++) {
    //     dccm_data = 0x00000000;
    //     dccm_data = lsu_read_32( 0x50000000 + 0x0001F000 + (ii * 4));
    //     VPRINTF(LOW, "MCU: Read DCCM data %d with 'h %0x\n", ii, dccm_data);
    // }

    for(uint8_t mctp_packet= 0; mctp_packet < 2; mctp_packet++)
    {
        VPRINTF(LOW, "MCU: reading MCTP packet %d\n", mctp_packet);
        //-- Wait for interrupt SOC_I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS
        while(1){
            i3c_reg_data = 0x00000000;
            i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS);
            i3c_reg_data &= I3CCSR_I3C_EC_TTI_INTERRUPT_STATUS_RX_DESC_STAT_MASK;
            if(i3c_reg_data == 0x00000000) {
                VPRINTF(LOW, "MCU: I3C TTI RX DESC Intrrupt is not set\n");
                for (uint8_t ii = 0; ii < 100; ii++)
                {
                    __asm__ volatile("nop"); // Sleep loop as "nop"
                }
            } else {
                VPRINTF(LOW, "MCU: I3C I3C TTI RX DESC Intrrupt is set\n");
                break;
            }  
        }
        
        // read SOC_I3CCSR_I3C_EC_TTI_RX_DESC_QUEUE_PORT 2 words
        i3c_reg_data = 0x00000000;
        i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_RX_DESC_QUEUE_PORT);
        VPRINTF(LOW, "MCU: Read I3C RX_DESC_QUEUE_PORT WORD1 with 'h %0x\n", i3c_reg_data);

        // read SOC_I3CCSR_I3C_EC_TTI_RX_DATA_PORT for 4 words
        for (uint8_t ii = 0; ii < 17; ii++) {
            i3c_reg_data = 0x00000000;
            i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_RX_DATA_PORT);
            VPRINTF(LOW, "MCU: Read I3C RX_DATA_PORT WORD%d with 'h %0x\n", ii, i3c_reg_data);
        }

    }
    
    VPRINTF(LOW, "MCU: End of I3C Reg Read Write Test\n");
    SEND_STDOUT_CTRL(0xff);
}