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
#include "soc_address_map.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "soc_ifc.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


#define exp_mbox_cmd                0x4d445554
#define MBOX_DLEN_VAL               9 // This plus 4 is for checksum
#define FUSE_CTRL_BASE_ADDR                             SOC_OTP_CTRL_BASE_ADDR
#define FUSE_CTRL_STATUS                                SOC_OTP_CTRL_STATUS
#define FUSE_CTRL_DIRECT_ACCESS_CMD                     SOC_OTP_CTRL_DIRECT_ACCESS_CMD
#define FUSE_CTRL_DIRECT_ACCESS_ADDRESS                 SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_0                 SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_1                 SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_0                 SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_0
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_1                 SOC_OTP_CTRL_DAI_RDATA_RF_DIRECT_ACCESS_RDATA_1

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};


inline void cpt_sleep (const uint32_t cycles) {
    for (uint8_t ii = 0; ii < cycles; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

uint32_t FC_base_addr;

uint32_t dma_read_from_lsu(uint32_t address){
    uint32_t read_data;
    soc_ifc_axi_dma_read_ahb_payload(address, 0, &read_data, 4, 0);
    return read_data;
}

void dma_write_from_lsu(uint32_t address, uint32_t write_data){
    soc_ifc_axi_dma_send_ahb_payload(address, 0, &write_data, 4, 0);
    return;
}


void wait_dai_op_idle(uint32_t status_mask) {
    uint32_t status;
    uint32_t dai_idle;
    uint32_t check_pending;

    const uint32_t error_mask = OTP_CTRL_STATUS_DAI_IDLE_MASK - 1;
    VPRINTF(LOW, "CLP_CORE: Waiting for DAI to become idle...\n");
    do {
        status = dma_read_from_lsu(FUSE_CTRL_STATUS);
        dai_idle = (status >> OTP_CTRL_STATUS_DAI_IDLE_LOW) & 0x1;
        check_pending = (status >> OTP_CTRL_STATUS_CHECK_PENDING_LOW) & 0x1;
    } while ((!dai_idle || check_pending) && ((status & error_mask) != error_mask));
    
    // Clear the IDLE bit from the status value
    status &= ((((uint32_t)1) << (OTP_CTRL_STATUS_DAI_IDLE_LOW - 1)) - 1);
    if ((status & error_mask) != status_mask) {
        VPRINTF(LOW, "ERROR: unexpected status: expected: %08X actual: %08X\n", status_mask, status);
    }
    VPRINTF(LOW, "DEBUG: DAI is now idle.\n");
    return;
}


void dai_rd(uint32_t addr, uint32_t* rdata0, uint32_t* rdata1, uint32_t granularity, uint32_t exp_status) {
    VPRINTF(LOW, "DEBUG: Starting DAI read operation...\n");

    //wait_dai_op_idle(0);

    VPRINTF(LOW, "DEBUG: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "CLP_CORE DEBUG: Triggering DAI read command.\n");
    dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_CMD, 0x1);

    wait_dai_op_idle(exp_status);

    *rdata0 = dma_read_from_lsu(FUSE_CTRL_DIRECT_ACCESS_RDATA_0);
    VPRINTF(LOW, "CLP_CORE DEBUG: Read data from DIRECT_ACCESS_RDATA_0: 0x%08X\n", *rdata0);

    if (granularity == 64) {
        *rdata1 = dma_read_from_lsu(FUSE_CTRL_DIRECT_ACCESS_RDATA_1);
        VPRINTF(LOW, "CLP_CORE DEBUG: Read data from DIRECT_ACCESS_RDATA_1: 0x%08X\n", *rdata1);
    }
    return;
}

void HEK_Read() {
    uint32_t base_address = 0x0D20;
    uint32_t data[2];
    int i;
    for (i=0;i<8;i++){
        dai_rd(base_address+i*4,  &data[0], &data[1], 32, 0);
        if (data[0] != 0x55AA55AA) {
            VPRINTF(LOW, "CLP_CORE ERROR: : HEK read failed at index %d: expected 0x55AA55AA, got 0x%08X \n", i, data[0]);
            return;
        }
    }
    uint32_t status_reg;
    status_reg = SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK;
    lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, status_reg);
    VPRINTF(LOW, "\n\nCLP_CORE: set SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK high 0x%X...\n\n", status_reg);
    
}



void HEK_Read_from_reg() {
    uint32_t base_address = CLP_SOC_IFC_REG_FUSE_HEK_SEED_3;
    int i;
    for (i=0;i<8;i++){
        uint32_t data = lsu_read_32(base_address + i*4);
        if (data != 0x55AA55AA) {
            VPRINTF(LOW, "CLP_CORE ERROR: : HEK read failed at index %d: expected 0x55AA55AA, got 0x%08X \n", i, data);
            return;
        }
    }
    uint32_t status_reg;
    status_reg = SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK;
    lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, status_reg);
    VPRINTF(LOW, "\n\nCLP_CORE: set SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK high 0x%X...\n\n", status_reg);
    
}


void main(void) {
    int argc=0;
    char *argv[1];

    VPRINTF(LOW,"----------------------------------\nCaliptra: Mimicking ROM from Subsystem!!\n----------------------------------\n");
    FC_base_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H);
    // HEK_Read();
    HEK_Read_from_reg();
    cpt_sleep(50000);

}
