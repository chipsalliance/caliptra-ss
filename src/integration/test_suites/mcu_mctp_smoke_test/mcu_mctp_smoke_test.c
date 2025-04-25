//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
//********************************************************************************
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
#include "veer-csr.h"

#define STATUS_CHECK_LOOP_COUNT_FOR_RECOVERY 20

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
// volatile char* stdout = (char *)0xd0580000;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint32_t global_data[] = {
    0x4E414D43, 0x0000423C, 0x00000001, 0x04000001,
    0xB7ABE77D, 0xB4E874BE, 0x6ACAEB9C, 0xF71B25C0,
    0xC0B5BF49, 0x41A78ECD, 0xCC6CD86D, 0xAEF3B805,
    0xF87DA21E, 0x5DD4E315, 0x920F45BA, 0xBB1E5146,
    0x3EDE83D4, 0x000000FA, 0x00000000, 0x00000000,
    0xD082E022, 0xC6044BB1, 0xA3C984E7, 0x6993DA18,
    0x76D0F3B1, 0x2D75CEC9, 0xC4ADC873, 0x30DBEA1F,
    0x37A9061E, 0x8433DA4E, 0x7E1439F4, 0x15F87DA2,
    0xB973ACC4, 0xB32FACF6, 0x5E48B272, 0x50EA5D0A,
    0x1A9F5587, 0x00000038, 0x00000000, 0x00000000,
    0x9F1983FA, 0xAF1A0BDF, 0x2F1E20B4, 0x3D1AA1B3,
    0xD09C13AF, 0xE79B91AF, 0x1D20A1B4, 0x9501CDE1,
    0xBD7338A9, 0x25F591A0, 0xEC116E8D, 0xBC0EC4A1,
    0xEECDA485, 0x8F98DD24, 0x45F20591, 0xD49D2C97,
    0x9E235798, 0x00000000, 0x00000000, 0x00000000,
    0x5C524C9C, 0xBB848F87, 0xB997F25B, 0xB32F72E2,
    0x13D37066, 0x0783B3E5, 0x24F8D85D, 0x0297688A,
    0x4E414D43, 0x0000423C, 0x00000001, 0x04000001,
    0xB7ABE77D, 0xB4E874BE, 0x6ACAEB9C, 0xF71B25C0,
    0xC0B5BF49, 0x00000000, 0x00000000, 0x00000000,
    0xD082E022, 0xC6044BB1, 0xA3C984E7, 0x6993DA18,
    0x76D0F3B1, 0x2D75CEC9, 0xC4ADC873, 0x30DBEA1F,
    0x37A9061E, 0x8433DA4E, 0x7E1439F4, 0x15F87DA2,
    0xB973ACC4, 0xB32FACF6, 0x5E48B272, 0x50EA5D0A,
    0xC873AB34, 0x00000000, 0x00000000, 0x00000000
};

void main (void) {

    int argc=0;
    char *argv[1];
    uint32_t i3c_reg_data;
    uint32_t error_status = 0;

    //-- Boot MCU
    VPRINTF(LOW, "MCU: Booting... \n");
    
    boot_mcu();
    boot_i3c_core();
    trigger_caliptra_go();
    wait_for_cptra_ready_for_mb_processing();
    configure_captra_axi_user();

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
        uint32_t dword_count; 
        dword_count =(((i3c_reg_data & 0x3) ? 1 : 0) + ((i3c_reg_data) >> 2));
        VPRINTF(LOW, "MCU: I3C RX_DESC_QUEUE_PORT DWORD count is %d\n", dword_count);

        
        // read SOC_I3CCSR_I3C_EC_TTI_RX_DATA_PORT for 4 words
        for (uint8_t ii = 0; ii < dword_count; ii++)
        {
            i3c_reg_data = 0x00000000;
            i3c_reg_data = lsu_read_32(SOC_I3CCSR_I3C_EC_TTI_RX_DATA_PORT);
            VPRINTF(LOW, "MCU: Read I3C RX_DATA_PORT WORD%d with 'h %0x\n", ii, i3c_reg_data);
            VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d data is 'h %0x\n", ii, i3c_reg_data);
            VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d reference data is 'h %0x\n", ii, global_data[ii+(mctp_packet*20)]);

            
            if (i3c_reg_data != (global_data[ii + (mctp_packet*20)])) // && ii != dword_count - 1) -- Exception For PEC
            {
                VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d data mismatch\n", ii);
                error_status = 1;

            } else {
                VPRINTF(LOW, "MCU: I3C RX_DATA_PORT WORD%d data match\n", ii);
            }
        }


    }
    
    VPRINTF(LOW, "MCU: End of I3C MCTP smoke test\n");
    
    if(error_status) {
        VPRINTF(LOW, "MCU: I3C MCTP smoke test failed\n");
        SEND_STDOUT_CTRL(0x01);
    } else {
        VPRINTF(LOW, "MCU: I3C MCTP smoke test passed\n");
        SEND_STDOUT_CTRL(0xff);
    }
}