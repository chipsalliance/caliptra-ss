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
#include "soc_ifc.h"
#include "soc_ifc_ss.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


volatile uint32_t* stdout           = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main(void) {
    uint32_t wr_data;
    uint32_t status;
    uint32_t payload[1] = {0};

    // If there is a protected MCU SRAM region do the following:
    // 1. Try to write to begin and end of protected region
    // 2. Try to read from begin and end of proteced region
    // This is negative testing the protected MCU SRAM region
    // the Caliptra DMA AXI USER should be randomized by the TB
    // or MCU.

    VPRINTF(LOW,"----------------------------------\nCaliptra MCU SRAM Protection Checks\n----------------------------------\n");
    uint32_t mcu_protection_region_start = cptra_get_mcu_sram_protection_region_start();
    uint32_t mcu_protection_region_end   = cptra_get_mcu_sram_last_dword(); // Default size

    if(cptra_is_sram_protected_region()) {
        wr_data = 0xFFFFFFFF;
        VPRINTF(LOW,"Caliptra: Writing protected region START: 0x%x with 0x%x\n", mcu_protection_region_start, wr_data);
        status = cptra_axi_dword_write_with_status(mcu_protection_region_start, wr_data);
        
        if(!status) {
            VPRINTF(FATAL,"Caliptra: ERROR Expected DMA ERROR Writing protected region START: 0x%x with 0x%x\n", mcu_protection_region_start, wr_data);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        
        VPRINTF(LOW,"Caliptra: Writing protected region END: 0x%x with 0x%x\n", mcu_protection_region_end, wr_data);
        status = cptra_axi_dword_write_with_status(mcu_protection_region_end, wr_data);
        
        if(!status) {
            VPRINTF(FATAL,"Caliptra: ERROR Expected DMA ERROR Writing protected region END: 0x%x with 0x%x\n", mcu_protection_region_end, wr_data);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        

        VPRINTF(LOW,"Caliptra: Reading protected region START: 0x%x\n", mcu_protection_region_start);
        status = cptra_axi_dword_read_with_status(mcu_protection_region_start, payload);
        
        if(!status) {
            VPRINTF(FATAL,"Caliptra: ERROR Expected DMA ERROR Reading protected region START: 0x%x with 0x%x\n", mcu_protection_region_start, wr_data);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(payload[0]) {
             VPRINTF(FATAL,"Caliptra: ERROR Expected DATA to be ZERO from rotected region START: 0x%x but got 0x%x\n", mcu_protection_region_start, payload[0]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        
        VPRINTF(LOW,"Caliptra: Reading protected region END: 0x%x\n", mcu_protection_region_end);
        status = cptra_axi_dword_read_with_status(mcu_protection_region_end, payload);
        
        if(!status) {
            VPRINTF(FATAL,"Caliptra: ERROR Expected DMA ERROR Reading protected region END: 0x%x with 0x%x\n", mcu_protection_region_end, wr_data);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(payload[0]) {
            VPRINTF(FATAL,"Caliptra: ERROR Expected DATA to be ZERO from rotected region END: 0x%x but got 0x%x\n", mcu_protection_region_end  , payload[0]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }
    else {
       VPRINTF(LOW,"Caliptra: MCU SRAM Protection Region doesn't exist"); 
    }

    VPRINTF(LOW, "Caliptra: TEST PASSED handshake with MCU to finish test\n");
    cptra_mcu_mbox_acquire_lock_set_execute(0, 100);

    cptra_mcu_mbox_wait_for_status_complete(0, 1000);

    while(1);

}
