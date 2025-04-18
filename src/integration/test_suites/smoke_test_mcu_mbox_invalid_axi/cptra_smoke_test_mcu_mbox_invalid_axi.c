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
#include "soc_ifc_ss.h"
#include "caliptra_reg.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Test (in conjuction with Caliptra uC C code) exercises invalid AXI and invalid SRAM address access 
// 1. MCU will configure Caliptra uC to be an invalid AXI
// 2. Caliptra uC will attempt CSR and SRAM read writes.  These are expected to return AXI errors

void main(void) {
    int argc=0;
    char *argv[1];
    uint32_t reg;
    uint32_t payload[1] = {0};
    uint32_t data_length;
    uint32_t data;
    uint32_t addr;
    uint32_t status;

    uint32_t mbox_num = decode_single_valid_mbox();

    VPRINTF(LOW, "----------------------------------\nSmoke Test MCI MBOX%x  !!\n----------------------------------\n", mbox_num);
    
    // Do SRAM and CSRs writes and reads and check that AXI errors are returned as expected
    // Writing and read to CSRs
    VPRINTF(LOW, "Caliptra: CSR Writes and Read as Invalid AXI\n");

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, 1);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR EXECUTE as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_EXECUTE + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading CSR EXECUTE as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR CMD as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading CSR CMD as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR CMD_STATUS as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_CMD_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading CSR CMD_STATUS as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR MBOX_USER as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading to CSR MBOX_USER as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR TARGET_USER as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading CSR TARGET_USER as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR TARGET_USER_VALID as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_TARGET_USER_VALID + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading CSR TARGET_USER_VALID as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR MBOX_DLEN as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_DLEN + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading to CSR MBOX_DLEN as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR LOCK as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading CSR LOCK as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, xorshift32());
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to CSR HW_STATUS as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_HW_STATUS + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
    if(!status) {
        VPRINTF(FATAL,"Caliptra: Expected AXI Error reading CSR HW_STATUS as invalid user\n", mbox_num);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    for(uint32_t i=0; i<8; i++) {
        data = xorshift32();
        addr = (xorshift32() % 131072)/4;  // Using 128KB
        VPRINTF(LOW, "Caliptra: Write to SRAM[%d]: 0x%x\n", addr, data);
        status = cptra_axi_dword_write_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + (4*addr) + MCU_MBOX_NUM_STRIDE * mbox_num, data);
        if(!status) {
            VPRINTF(FATAL,"Caliptra: Expected AXI Error writing to Mbox%x SRAM as invalid user\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        addr = (xorshift32() % 131072)/4;
        VPRINTF(LOW, "Caliptra: Read from SRAM[%d]\n", addr);
        status = cptra_axi_dword_read_with_status(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_SRAM_BASE_ADDR + (4*addr) + MCU_MBOX_NUM_STRIDE * mbox_num, payload);
        if(!status) {
            VPRINTF(FATAL,"Caliptra: Expected AXI Error reading Mbox%x SRAM as invalid user\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
    }

    VPRINTF(LOW, "CALIPTRA: Sequence complete\n");

    SEND_STDOUT_CTRL(0xff);
}
