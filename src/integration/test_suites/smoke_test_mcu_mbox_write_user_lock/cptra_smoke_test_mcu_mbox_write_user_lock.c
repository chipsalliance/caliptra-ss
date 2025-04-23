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
#include "caliptra_ss_lib.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdbool.h>
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

bool caliptra_ss_mcu_mbox_acquire_lock(uint32_t mbox_num, uint32_t attempt_count) {
    uint32_t read_payload[1];
    uint32_t mbox_data;
    uint32_t mbox_lock_accuired;
    for(uint32_t ii=0; ii<attempt_count; ii++) {
        soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);
        mbox_data = read_payload[0];
        mbox_lock_accuired = mbox_data & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK;
        if(mbox_lock_accuired == 0) {
            return true;
        }
    }
    return false;
}

void caliptra_ss_mcu_mbox_send_data_no_wait_status(uint32_t mbox_num) {
    uint32_t data_length;
    uint32_t read_payload[16];
    uint32_t write_payload[16];
    uint32_t mbox_data[0];
    VPRINTF(LOW, "CALIPTRA: Requesting MCU MBOX%x LOCK\n", mbox_num);
    if (!caliptra_ss_mcu_mbox_acquire_lock(mbox_num, 32)) {
        VPRINTF(FATAL, "CALIPTRA: MCU MBOX%x Lock Not Acquired\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Checking MBOX USER INFO
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, 0, read_payload, 4, 0);     
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x USER: 0x%x\n", mbox_num, read_payload[0]);

    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x SETTING COMMAND\n", mbox_num);
    write_payload[0] = 0xDEADBEEF;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);
    
    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x SETTING DLEN\n", mbox_num);
    write_payload[0] = 16*4;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);

    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x SETTING DATA\n", mbox_num);
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
        VPRINTF(LOW, "CALIPTRA: Writing to MBOX%x data: 0x%x\n", mbox_num, write_payload[ii]); 
        soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR+(4*ii) + MCU_MBOX_NUM_STRIDE * mbox_num, 0, mbox_data, 4, 0);
    }

    VPRINTF(LOW, "CALIPTRA: MCU MBOX%x SETTING EXECUTE\n", mbox_num);
    write_payload[0] = 0x1;
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 0, write_payload, 4, 0);
}

void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint32_t read_payload[16];
        uint32_t data_length;
        uint32_t write_payload[16];

        #ifdef MCU_MBOX_VALID_VECTOR
            int32_t mbox_instances = MCU_MBOX_VALID_VECTOR;
        #else
            uint32_t mbox_instances = 0;
        #endif

        uint32_t mbox_num = 0;
        if (mbox_instances == 0x2) {
            mbox_num = 1;
        }

        VPRINTF(LOW, "----------------------------------\nSmoke Test MCI MBOX%x  !!\n----------------------------------\n", mbox_num);

        caliptra_ss_mcu_mbox_send_data_no_wait_status(mbox_num);

        VPRINTF(LOW, "CALIPTRA: Sequence complete\n");
        while(1);
}
