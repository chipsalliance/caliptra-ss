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
#include "recovery_ifc.h"
#include "soc_address_map.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


// Wait function
void wait(uint32_t wait_time) {
    for (uint32_t ii = 0; ii < wait_time; ii++) {
        for (uint8_t jj = 0; jj < 16; jj++) {
            __asm__ volatile ("nop");
        }
    }
}

void wait_for_write_to_prot_cap_0(uint32_t recovery_ifc_start_addr) {
    // reading INDIRECT_FIFO_STATUS
    uint32_t i3c_reg_data;
    while (1) {
        i3c_reg_data = 0x00000000;
        soc_ifc_axi_dma_read_ahb_payload(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_PROT_CAP_0 , 0, &i3c_reg_data, 4, 0);
        VPRINTF(LOW, "CPTRA: INDIRECT_FIFO_STATUS is 'h %0x\n", i3c_reg_data);
        //-- check if FIFO is empty by reading bit 0 as 1'b1
        if (i3c_reg_data == 0x00000000) {
            VPRINTF(LOW, "CPTRA: PROT_CAP_0 is zero\n");
            wait(100);
        } else {
            VPRINTF(LOW, "CPTRA: PROT_CAP_0 is updated\n");
            break;
        }
    }
}

void read_i3c_reg(uint32_t i3c_reg_addr, char *reg_name) {
    uint32_t i3c_reg_data;
    soc_ifc_axi_dma_read_ahb_payload(i3c_reg_addr, 0, &i3c_reg_data, 4, 0);
    VPRINTF(LOW, "CPTRA: Read %s with 'h %0x\n", reg_name, i3c_reg_data);
}

void read_i3c_registers(uint32_t recovery_ifc_start_addr) {
    uint32_t i3c_reg_data;
    // read PROT_CAP
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_PROT_CAP_0, "PROT_CAP_0");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_PROT_CAP_1, "PROT_CAP_1");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_PROT_CAP_2, "PROT_CAP_2");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_PROT_CAP_3, "PROT_CAP_3");
    // Read DEVICE_ID
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_ID_0, "DEVICE_ID_0");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_ID_1, "DEVICE_ID_1");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_ID_2, "DEVICE_ID_2");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_ID_3, "DEVICE_ID_3");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_ID_4, "DEVICE_ID_4");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_ID_5, "DEVICE_ID_5");
    // Read DEVICE_STATUS
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_STATUS_0, "DEVICE_STATUS_0");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_DEVICE_STATUS_1, "DEVICE_STATUS_1");
    // Read HW_STATUS
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_HW_STATUS, "HW_STATUS");
    // Read RECOVERY_CTRL
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_RECOVERY_CTRL, "RECOVERY_CTRL");
    // Read RECOVERY_STATUS
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_RECOVERY_STATUS, "RECOVERY_STATUS");
    // Read INDIRECT_FIFO_CTRL
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_INDIRECT_FIFO_CTRL_0, "INDIRECT_FIFO_CTRL_0");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_INDIRECT_FIFO_CTRL_1, "INDIRECT_FIFO_CTRL_1");
    // Read INDIRECT_FIFO_STATUS
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_INDIRECT_FIFO_STATUS_0, "INDIRECT_FIFO_STATUS_0");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_INDIRECT_FIFO_STATUS_1, "INDIRECT_FIFO_STATUS_1");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_INDIRECT_FIFO_STATUS_2, "INDIRECT_FIFO_STATUS_2");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_INDIRECT_FIFO_STATUS_3, "INDIRECT_FIFO_STATUS_3");
    read_i3c_reg(recovery_ifc_start_addr + RECOVERY_IFC_OFFSET_INDIRECT_FIFO_STATUS_4, "INDIRECT_FIFO_STATUS_4");
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

    // FIXME : Depends on, Assertion issue, DMA write strobe issue. 
    // "/home/ws/caliptra/pateln/caliptra_ws_250317/Caliptra/src/libs/arm_licensed/BP063-BU-01000-r0p1-00rel0/sva/Axi4PC.sv", 1733: caliptra_ss_top_tb.axi_interconnect.master_mon[3].monitor.checker0.axi4_errm_wstrb: started at 116405000ps failed at 116405000ps
    // 	Offending '(~BStrbError)'
    // Error: "/home/ws/caliptra/pateln/caliptra_ws_250317/Caliptra/src/libs/arm_licensed/BP063-BU-01000-r0p1-00rel0/sva/Axi4PC.sv", 1733: caliptra_ss_top_tb.axi_interconnect.master_mon[3].monitor.checker0.axi4_errm_wstrb: at time 116405000 ps
    // AXI4_ERRM_WSTRB: Write strobes must only be asserted for the correct byte lanes as determined from start address, transfer size and beat number. Spec: section A3.4.3.
    
    // FIXME : Uncomment when above issue is resolved. 

    // // Send data through AHB interface to AXI_DMA, target the AXI SRAM
    // VPRINTF(LOW, "Sending payload via AHB i/f\n");
    // soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, send_payload, 16, 0);
    
    // // Move data from one address to another in AXI SRAM
    // // Use the block-size feature
    // VPRINTF(LOW, "Reading payload at SRAM via AHB i/f\n");
    // soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, read_payload, 16, 0);
    //set ready for FW so tb will push FW
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Read Recovery Interface Offset
    VPRINTF(LOW, "CPTRA: Reading Recovery Interface start Addr\n");
    uint32_t recovery_ifc_start_addr = 0x00000000;
    // read -- CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L
    recovery_ifc_start_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L);
    VPRINTF(LOW, "CPTRA: Recovery Interface start Addr is 'h %0x\n", recovery_ifc_start_addr);

    // Read Recovery Interface Offset
    VPRINTF(LOW, "CPTRA: Reading Recovery Interface start Addr\n");
    // read -- CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L
    recovery_ifc_start_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L);
    VPRINTF(LOW, "CPTRA: Recovery Interface start Addr is 'h %0x\n", recovery_ifc_start_addr);

    // Read I3C registers
    wait_for_write_to_prot_cap_0(recovery_ifc_start_addr);
    read_i3c_registers(recovery_ifc_start_addr);
    wait(100000);

    VPRINTF(LOW, "End of Caliptra Test\n");

    if (fail) {
        VPRINTF(FATAL, " cptra_ss_test_rom failed!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}