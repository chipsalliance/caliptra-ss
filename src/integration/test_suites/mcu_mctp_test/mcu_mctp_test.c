

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

// reference data for the I3C device
uint8_t global_data[] = {
    0x43, 0x4D, 0x41, 0x4E, 0x3C, 0x42, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x04,
    0x7D, 0xE7, 0xAB, 0xB7, 0xBE, 0x74, 0xE8, 0xB4, 0x9C, 0xEB, 0xCA, 0x6A, 0xC0, 0x25, 0x1B, 0xF7,
    0x49, 0xBF, 0xB5, 0xC0, 0xCD, 0x8E, 0xA7, 0x41, 0x6D, 0xD8, 0x6C, 0xCC, 0x05, 0xB8, 0xF3, 0xAE,
    0x1E, 0xA2, 0x7D, 0xF8, 0x15, 0xE3, 0xD4, 0x5D, 0xBA, 0x45, 0x0F, 0x92, 0x46, 0x51, 0x1E, 0xBB,
    0xD4, 0x83, 0xDE, 0x3E, 0x22, 0xE0, 0x82, 0xD0, 0xB1, 0x4B, 0x04, 0xC6, 0xE7, 0x84, 0xC9, 0xA3,
    0x18, 0xDA, 0x93, 0x69, 0xB1, 0xF3, 0xD0, 0x76, 0xC9, 0xCE, 0x75, 0x2D, 0x73, 0xC8, 0xAD, 0xC4,
    0x1F, 0xEA, 0xDB, 0x30, 0x1E, 0x06, 0xA9, 0x37, 0x4E, 0xDA, 0x33, 0x84, 0xF4, 0x39, 0x14, 0x7E,
    0xC4, 0xAC, 0x73, 0xB9, 0xF6, 0xAC, 0x2F, 0xB3, 0x72, 0xB2, 0x48, 0x5E, 0x0A, 0x5D, 0xEA, 0x50,
    0x87, 0x55, 0x9F, 0x1A, 0x22, 0x9F, 0x0E, 0x1C, 0x09, 0x6E, 0x51, 0xDA, 0x11, 0xC3, 0xC1, 0xA9,
    0xFA, 0x83, 0x19, 0x9F, 0xDF, 0x0B, 0x1A, 0xAF, 0xB4, 0x20, 0x1E, 0x2F, 0xB3, 0xA1, 0x1A, 0x3D,
    0xAF, 0x13, 0x9C, 0xD0, 0xAF, 0x91, 0x9B, 0xE7, 0xB4, 0xA1, 0x20, 0x1D, 0xE1, 0xCD, 0x01, 0x95,
    0xA9, 0x38, 0x73, 0xBD, 0xA0, 0x91, 0xF5, 0x25, 0x8D, 0x6E, 0x11, 0xEC, 0xA1, 0xC4, 0x0E, 0xBC,
    0x85, 0x4A, 0xCD, 0xEE, 0x24, 0xDD, 0x98, 0x8F, 0x91, 0x05, 0xF2, 0x45, 0x97, 0x2C, 0x9D, 0xD4,
    0x01, 0x00, 0x01, 0x04, 0xB5, 0x2D, 0x40, 0x98, 0xAD, 0xE9, 0x83, 0x11, 0x3B, 0xEB, 0x06, 0x81,
    0x98, 0x57, 0x23, 0x9E, 0x24, 0xAE, 0x49, 0x07, 0xE7, 0xA2, 0xF1, 0xF6, 0x9F, 0xFD, 0x1D, 0x00,
    0x9C, 0x4C, 0x52, 0x5C, 0x87, 0x8F, 0x84, 0xBB, 0x5B, 0xF2, 0x97, 0xB9, 0xE2, 0x72, 0x2F, 0xB3,
    0x66, 0x70, 0xD3, 0x13, 0xE5, 0xB3, 0x83, 0x07, 0x5D, 0xD8, 0xF8, 0x24, 0x8A, 0x68, 0x97, 0x02
};

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
        
        // read SOC_I3CCSR_I3C_EC_TTI_RX_DESC_QUEUE_PORT 1 words
        i3c_reg_data = 0x00000000;
        i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_RX_DESC_QUEUE_PORT);
        VPRINTF(LOW, "MCU: Read I3C RX_DESC_QUEUE_PORT WORD1 with 'h %0x\n", i3c_reg_data);

        // convert byte count to DWORD count if not DWORD aligned, add 1
        uint32_t dword_count = ((i3c_reg_data & 0x3) ? 1 : 0) + (i3c_reg_data) >> 2;
        VPRINTF(LOW, "MCU: I3C RX_DESC_QUEUE_PORT DWORD count is %d\n", dword_count);


        // read SOC_I3CCSR_I3C_EC_TTI_RX_DATA_PORT for 4 words
        for (uint8_t ii = 0; ii < dword_count; ii++)
        {
            uint32_t ref_data;
            ref_data  = global_data[mctp_packet*16 + ii*4 + 3] << 24;
            ref_data |= global_data[mctp_packet*16 + ii*4 + 2] << 16;
            ref_data |= global_data[mctp_packet*16 + ii*4 + 1] << 8;
            ref_data |= global_data[mctp_packet*16 + ii*4 + 0];

            i3c_reg_data = 0x00000000;
            i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_RX_DATA_PORT);
            VPRINTF(LOW, "MCU: Read I3C RX_DATA_PORT WORD%d with 'h %0x\n", ii, i3c_reg_data);

            // FIXME : Add a check for the last word - PEC verification
            if (i3c_reg_data != ref_data && ii != dword_count - 1) 
            {
                VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d data mismatch\n", ii);
                VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d data is 'h %0x\n", ii, i3c_reg_data);
                VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d reference data is 'h %0x\n", ii, ref_data);
            } else {
                VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d data match\n", ii);
            }
        }


    }
    
    VPRINTF(LOW, "MCU: End of I3C Reg Read Write Test\n");
    SEND_STDOUT_CTRL(0xff);
}