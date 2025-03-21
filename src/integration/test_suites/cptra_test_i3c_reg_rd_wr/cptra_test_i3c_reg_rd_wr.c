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
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_reg.h"
#include "soc_address_map.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Function Name : update_recovery_status
void update_recovery_status(uint32_t recovery_status) {
    
    uint32_t i3c_reg_data; 
    
    // Write RECOVERY_STATUS
    // 0x0: Not in recovery mode
    // 0x1: Awaiting recovery image
    // 0x2: Booting recovery image
    // 0x3: Recovery successful
    // 0xc: Recovery failed
    // 0xd: Recovery image authentication error
    // 0xe: Error entering  Recovery mode (might be administratively disabled)
    // 0xf: Invalid component address space

    i3c_reg_data = recovery_status;

    switch (recovery_status) {
        case 0x0:
            VPRINTF(LOW, "CPTRA: Recovery Status is Not in recovery mode\n");
            break;
        case 0x1:
            VPRINTF(LOW, "CPTRA: Recovery Status is Awaiting recovery image\n");
            break;
        case 0x2:
            VPRINTF(LOW, "CPTRA: Recovery Status is Booting recovery image\n");
            break;
        case 0x3:
            VPRINTF(LOW, "CPTRA: Recovery Status is Recovery successful\n");
            break;
        case 0xc:
            VPRINTF(LOW, "CPTRA: Recovery Status is Recovery failed\n");
            break;
        case 0xd:
            VPRINTF(LOW, "CPTRA: Recovery Status is Recovery image authentication error\n");
            break;
        case 0xe:
            VPRINTF(LOW, "CPTRA: Recovery Status is Error entering Recovery mode (might be administratively disabled)\n");
            break;
        case 0xf:
            VPRINTF(LOW, "CPTRA: Recovery Status is Invalid component address space\n");
            break;
        default:
            VPRINTF(ERROR, "CPTRA: Invalid recovery status value\n");
    }
    
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, 0, &i3c_reg_data, 4, 0);
    
}

// 	Read  INDIRECT_FIFO_CTRL_0 (Byte 2,3) for the Image Size
// 	Read  INDIRECT_FIFO_CTRL_1 (Byte 0,1) for the Image Size
// Combine Byte{1,0,3,2} for Size of the image to be loaded in 4B units
uint32_t read_image_size(){

    uint32_t i3c_reg_data;
    uint32_t img_size;
    uint32_t loop_count = 0;
    
    VPRINTF(LOW, "CPTRA: Reading Image Size from INDIRECT_FIFO_CTRL_1 Register\n");
    img_size = 0x00000000;

    while (img_size == 0x00000000) {
        // Read INDIRECT_FIFO_CTRL_1
        soc_ifc_axi_dma_read_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1, 0, &i3c_reg_data, 4, 0);
        VPRINTF(LOW, "CPTRA: Reading SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1 with 'h %0x\n", i3c_reg_data);
        img_size = i3c_reg_data;
        VPRINTF(LOW, "CPTRA: Image Size is 'h %0x , 'd %0d\n", img_size, img_size);

        if (img_size == 0x00000000) {
            VPRINTF(LOW, "CPTRA: Image Size is not available yet\n");
            for (uint8_t ii = 0; ii < 160; ii++) {
                __asm__ volatile ("nop");
            }
        }
        loop_count++;
        if (loop_count > 1000) {
            VPRINTF(ERROR, "CPTRA: Image Size not available after 1000 attempts\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop");
    }

    // Read INDIRECT_FIFO_CTRL_1
    soc_ifc_axi_dma_read_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1, 0, &i3c_reg_data, 4, 0);
    VPRINTF(LOW, "CPTRA: Reading SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1 with 'h %0x\n", i3c_reg_data);
    img_size = i3c_reg_data;
    VPRINTF(LOW, "CPTRA: Image Size is 'h %0x , 'd %0d\n", img_size, img_size);

    
    return img_size;

}

// Wait function
void wait(uint32_t wait_time) {
    for (uint32_t ii = 0; ii < wait_time; ii++) {
        for (uint8_t jj = 0; jj < 16; jj++) {
            __asm__ volatile ("nop");
        }
    }
}

// Recovery Sequence
void recovery_sequence() {
    
    uint32_t fw_image_size;

    update_recovery_status(0x1); // Awaiting recovery image
    fw_image_size = read_image_size();
    SEND_STDOUT_CTRL(0xff);
        
}

void main(void) {
    
    int argc=0;
    char *argv[1];
    uint32_t reg;
    uint8_t fail = 0;

    uint32_t send_payload[4] = {0xabadface, 0xba5eba11, 0xcafebabe, 0xdeadbeef};
    uint32_t read_payload[16];

    VPRINTF(LOW, "----------------------------------\n Caliptra SS Test Streaming Boot\n----------------------------------\n");

    // Setup the interrupt CSR configuration
    // init_interrupts();
    fail = 0;

    // Send data through AHB interface to AXI_DMA, target the AXI SRAM
    VPRINTF(LOW, "Sending payload via AHB i/f\n");
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, &send_payload, 16, 0);
    
    // Move data from one address to another in AXI SRAM
    // Use the block-size feature
    VPRINTF(LOW, "Reading payload at SRAM via AHB i/f\n");
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, &read_payload, 16, 0);

    //set ready for FW so tb will push FW
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    VPRINTF(LOW, "Initiating Recovery Sequence\n");
    recovery_sequence();  

    if (fail) {
        VPRINTF(FATAL, " cptra_ss_test_rom failed!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}
