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
#include "soc_address_map.h"
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "soc_ifc.h"
#include "caliptra_reg.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

uint8_t caliptra_ss_mcu_mbox0_acquire_lock(uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_lock_accuired = mbox_data & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK;
        if(mbox_lock_accuired == 0) {
            return 0;
        }
    }
    return 1;
}


uint8_t caliptra_ss_mcu_mbox0_wait_execute(uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 WAIT FOR EXECUTE to be SET\n");
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX1_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        if( mbox_data) {
            return 0;
        }
    }
    return 1;
}

uint32_t caliptra_ss_mcu_mbox0_wait_status_complete(uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 WAIT FOR COMPLETE\n");
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_data = mbox_data & MCU_MBOX0_CSR_MBOX_CMD_STATUS_STATUS_MASK;
        VPRINTF(LOW, "CALIPTRA: MBOX STATUS: 0x%x\n", mbox_data);
        if (mbox_data == 0x2) {
            return mbox_data;
        }
    }
    return 1;
}
uint8_t caliptra_ss_mcu_mbox0_clear_execution() {
    uint8_t fail = 0;
    uint32_t data_length;
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    
    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 CLEARING EXECUTE\n");
    write_payload[0] = 0x0;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, 0, write_payload, 4, 0) ;

    return fail;
}
uint8_t caliptra_ss_mcu_mbox0_send_data_no_wait_status() {
    uint8_t fail = 0;
    uint32_t data_length;
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    uint32_t mbox_data[0];
    VPRINTF(LOW, "CALIPTRA: Requesting MCU MBOX0 LOCK\n");
    fail = caliptra_ss_mcu_mbox0_acquire_lock(32);
    if (fail) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX0 Lock Not Acquired\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Checking MBOX USER INFO
    if (!fail) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER, 0, read_payload, 4, 0);
         
    }
    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 USER: 0x%x\n", read_payload[0]);

    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 SETTING COMMAND\n");
    write_payload[0] = 0xDEADBEEF;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD, 0, write_payload, 4, 0);
    
    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 SETTING DLEN\n");
    write_payload[0] = 16*4;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, 0, write_payload, 4, 0);

    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 SETTING DATA\n");
    write_payload[0] = 0x10101010;
    write_payload[1] = 0x20202020;
    write_payload[2] = 0x30303030;
    write_payload[3] = 0x40404040;
    write_payload[4] = 0x50505050;
    write_payload[5] = 0x60606060;
    write_payload[6] = 0x70707070;
    write_payload[7] = 0x80808080;
    write_payload[8] = 0x90909090;
    write_payload[9] = 0xA0A0A0A0;
    write_payload[10] = 0xB0B0B0B0;
    write_payload[11] = 0xC0C0C0C0;
    write_payload[12] = 0xD0D0D0D0;
    write_payload[13] = 0xE0E0E0E0;
    write_payload[14] = 0xF0F0F0F0;
    write_payload[15] = 0x12345678;
    
    for (uint32_t ii = 0; ii < 16; ii++) {
        mbox_data[0] = write_payload[ii];
        VPRINTF(LOW, "CALIPTRA: Writing to MBOX data: 0x%x\n", write_payload[ii]); 
        soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii), 0, mbox_data, 4, 0);
    }

    VPRINTF(LOW, "CALIPTRA: MCU MBOX0 SETTING EXECUTE\n");
    write_payload[0] = 0x1;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE, 0, write_payload, 4, 0);
    return fail;
}

uint8_t caliptra_ss_mcu_mbox0_get_data() {
    uint8_t fail = 0;
    uint32_t data_length;
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    uint32_t mcu_expected_data[] = { 0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000,
                                    0x00000000 };

    
    fail = caliptra_ss_mcu_mbox0_wait_execute(300);
    
    VPRINTF(LOW, "CALIPTRA: Reading MBOX DLEN\n");
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN, 0, read_payload, 4, 0);
    data_length = read_payload[0];
    VPRINTF(LOW, "CALIPTRA: DLEN: 0x%x\n", data_length);


    VPRINTF(LOW, "CALIPTRA: Reading MBOX Data\n");
    for (uint8_t ii = 0; ii < data_length/4; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii), 0, read_payload, 4, 0);
        VPRINTF(LOW, "CALIPTRA: MBOX Data[%d]: 0x%x\n", ii, read_payload[0]);
        if (read_payload[0] != mcu_expected_data[ii]) {
            VPRINTF(FATAL, "Mbox0 SRAM data from MCU is not expected value - dword: %x, Expected: 0x%x Actual: 0x%x\n", ii, mcu_expected_data[ii], read_payload[0]);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }
    
    return fail;

}


void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint8_t fail = 0;
        uint32_t read_payload[16];
        uint32_t data_length;
        uint32_t write_payload[16];

        VPRINTF(LOW, "----------------------------------\nSmoke Test MCI MBOX0  !!\n----------------------------------\n");

        fail = caliptra_ss_mcu_mbox0_send_data_no_wait_status();
        if (fail) {
            VPRINTF(FATAL, "CALIPTRA: FAILED!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        
        reg = caliptra_ss_mcu_mbox0_wait_status_complete(200);
        if (reg == 2) {
            caliptra_ss_mcu_mbox0_clear_execution();    
        } else {
            VPRINTF(FATAL, "CALIPTRA: Timed out waiting for MBOX complete\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        fail = caliptra_ss_mcu_mbox0_get_data();
        if (fail) {
            VPRINTF(FATAL, "CALIPTRA: FAILED\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

}
