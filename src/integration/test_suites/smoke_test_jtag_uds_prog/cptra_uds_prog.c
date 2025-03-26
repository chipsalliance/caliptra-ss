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
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"



/*
#### UDS Provisioning
1. On reset, the ROM checks if the `UDS_PROGRAM_REQ` bit in the `SS_DBG_MANUF_SERVICE_REG_REQ` register is set. If the bit is set, ROM initiates the UDS seed programming flow by setting the `UDS_PROGRAM_IN_PROGRESS` bit in the `SS_DBG_MANUF_SERVICE_REG_RSP` register. If the flow fails at some point past reading the REQ bits, the flow will be aborted and an error returned.

2. ROM then retrieves a 512-bit value from the iTRNG, the UDS Seed programming base address from the `SS_UDS_SEED_BASE_ADDR_L` and `SS_UDS_SEED_BASE_ADDR_H` registers and the Fuse Controller's base address from the `SS_OTP_FC_BASE_ADDR_L` and `SS_OTP_FC_BASE_ADDR_H` registers.

3. ROM then retrieves the UDS granularity from the `CPTRA_HW_CONFIG` register Bit6 to learn if the fuse row is accessible with 32-bit or 64-bit granularity.

4. ROM then performs the following steps until all the 512 bits of the UDS seed are programmed:
    1. The ROM verifies the idle state of the DAI by reading the `STATUS` register `DAI_IDLE` bit (Bit-21) of the Fuse Controller, located at offset 0x10 from the Fuse Controller's base address.
    2. If the granularity is 32-bit, the ROM writes the next word from the UDS seed to the `DIRECT_ACCESS_WDATA_0` register. If the granularity is 64-bit, the ROM writes the next two words to `the DIRECT_ACCESS_WDATA_0` and `DIRECT_ACCESS_WDATA_1` registers, located at offsets 0x44 and 0x48 respectively from the Fuse Controller's base address.
    3. The ROM writes the lower 32 bits of the UDS Seed programming base address to the `DIRECT_ACCESS_ADDRESS` register at offset 0x40.
    4. The ROM triggers the UDS seed write command by writing 0x2 to the `DIRECT_ACCESS_CMD` register at offset 0x3C.
    5. The ROM increments the `DIRECT_ACCESS_ADDRESS` register by 4 for 32-bit granularity or 8 for 64-bit granularity and repeats the process for the remaining words of the UDS seed.

5. The ROM continuously polls the Fuse Controller's `STATUS` register until the DAI state returns to idle.

6. After completing the write operation, ROM triggers the partition  digest operation performing the following steps:
    1. The ROM writes the lower 32 bits of the UDS Seed programming base address to the `DIRECT_ACCESS_ADDRESS` register.
    2. The ROM triggers the digest calculation command by writing 0x4 to the `DIRECT_ACCESS_CMD` register.
    3. The ROM continuously polls the Fuse Controller's `STATUS` register until the DAI state returns to idle.

7. ROM updates the `UDS_PROGRAM_SUCCESS` or the `UDS_PROGRAM_FAIL` bit in the `SS_DBG_MANUF_SERVICE_REG_RSP` register to indicate the outcome of the operation.

8. ROM then resets the `UDS_PROGRAM_IN_PROGRESS` bit in the `SS_DBG_MANUF_SERVICE_REG_RSP` register to indicate completion of the programming.

9. The manufacturing process then polls this bit and continues with the fuse burning flow as outlined by the fuse controller specifications and SOC-specific VR methodologies.
*/


volatile uint32_t* stdout           = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t  intr_count;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define FUSE_CTRL_BASE_ADDR (0x70000000)
#define FUSE_CTRL_STATUS                                                      (FUSE_CTRL_BASE_ADDR + 0x010)
#define FUSE_CTRL_DIRECT_ACCESS_CMD                                           (FUSE_CTRL_BASE_ADDR + 0x060)
#define FUSE_CTRL_DIRECT_ACCESS_ADDRESS                                       (FUSE_CTRL_BASE_ADDR + 0x064)
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_0                                       (FUSE_CTRL_BASE_ADDR + 0x068)
#define FUSE_CTRL_DIRECT_ACCESS_WDATA_1                                       (FUSE_CTRL_BASE_ADDR + 0x06C)
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_0                                       (FUSE_CTRL_BASE_ADDR + 0x070)
#define FUSE_CTRL_DIRECT_ACCESS_RDATA_1                                       (FUSE_CTRL_BASE_ADDR + 0x074)
#define FUSE_CTRL_STATUS_DAI_IDLE_OFFSET (22)

uint32_t dma_read_from_lsu(uint32_t address){
    uint32_t read_data;
    soc_ifc_axi_dma_read_ahb_payload(address, 0, &read_data, 4, 0);
    return read_data;
}

void dma_write_from_lsu(uint32_t address, uint32_t write_data){
    soc_ifc_axi_dma_send_ahb_payload(address, 0, &write_data, 16, 0);
    return;
}

void wait_dai_op_idle(uint32_t status_mask) {
    uint32_t status;
    VPRINTF(LOW, "CLP_CORE: Waiting for DAI to become idle...\n");
    do {
        status = dma_read_from_lsu(FUSE_CTRL_STATUS);
    } while (((status >> FUSE_CTRL_STATUS_DAI_IDLE_OFFSET) & 0x1) == 0);
    // Clear the IDLE bit from the status value
    status &= ((((uint32_t)1) << (FUSE_CTRL_STATUS_DAI_IDLE_OFFSET - 1)) - 1);
    if (status != status_mask) {
        VPRINTF(LOW, "CLP_CORE ERROR: unexpected status: expected: %08X actual: %08X\n", status_mask, status);
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK);
        printf("%c",0xff); //End the test
    }
    VPRINTF(LOW, "CLP_CORE: DAI is now idle.\n");
    return;
}

void dai_wr(uint32_t addr, uint32_t wdata0, uint32_t wdata1, uint32_t granularity, uint32_t exp_status) {
    VPRINTF(LOW, "CLP_CORE: Starting DAI write operation...\n");

    //wait_dai_op_idle(0);

    VPRINTF(LOW, "CLP_CORE: Writing wdata0: 0x%08X to DIRECT_ACCESS_WDATA_0.\n", wdata0);
    dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_WDATA_0, wdata0);

    if (granularity == 64) {
        VPRINTF(LOW, "CLP_CORE: Writing wdata1: 0x%08X to DIRECT_ACCESS_WDATA_1.\n", wdata1);
        dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_WDATA_1, wdata1);
    }

    VPRINTF(LOW, "CLP_CORE: Writing address: 0x%08X to DIRECT_ACCESS_ADDRESS.\n", addr);
    dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_ADDRESS, addr);

    VPRINTF(LOW, "CLP_CORE: Triggering DAI write command.\n");
    dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_CMD, 0x2);

    wait_dai_op_idle(exp_status);
    return;
}

void calculate_digest(uint32_t partition_base_address) {
    // Step 1: Check if DAI is idle
    wait_dai_op_idle(0);

    // Step 2: Write the partition base address to DIRECT_ACCESS_ADDRESS
    dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_ADDRESS, partition_base_address);
    VPRINTF(LOW, "CLP_CORE: Partition base address 0x%08X written to DIRECT_ACCESS_ADDRESS.\n", partition_base_address);

    // Step 3: Trigger a digest calculation command
    dma_write_from_lsu(FUSE_CTRL_DIRECT_ACCESS_CMD, 0x4);

    // Step 4: Poll STATUS until DAI state goes back to idle    
    wait_dai_op_idle(0);
    return;
}

void UDS_provision(uint32_t base_address) {

    // 0x580: CPTRA_SS_TEST_EXIT_TO_MANUF_TOKEN
    int i;
    for (i=0;i<1;i++){
        dai_wr(base_address, i*2, i*2+1, 64, 0);
        VPRINTF(LOW, "CLP_CORE: programming %02d item in UDS partition with 0x%08X and 0x%08X...\n",i, i*2, i*2+1);
    }

    calculate_digest(base_address);
    VPRINTF(LOW, "CLP_CORE: triggered digest operation\n");

    wait_dai_op_idle(0);
}

void main(void) {
    int argc=0;
    char *argv[1];

    VPRINTF(LOW,"----------------------------------\nCaliptra: Mimicking ROM from Subsystem!!\n----------------------------------\n");
    uint32_t status_reg = 0;
    status_reg = (lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ) & SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK) == SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK;
    if (status_reg){
        VPRINTF(LOW, "CLP_CORE: detected UDS prog request...\n");
        status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP);
        status_reg = status_reg | SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK;
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, status_reg);
        VPRINTF(LOW, "CLP_CORE: set DBG_MANUF_SERVICE_REG_RSP high...\n");
        uint32_t UDS_low_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L);
        uint32_t UDS_high_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H);
        uint32_t FC_base_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H);
        UDS_provision(FC_base_addr+UDS_low_addr);
        status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP);
        status_reg = status_reg | SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK;
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, status_reg);
        VPRINTF(LOW, "CLP_CORE: set RSP_UDS_PROGRAM_SUCCESS high...\n");
        status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP);
        status_reg = status_reg & (SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK ^ 0xFFFFFFFF);
        lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP, status_reg);
        while(1);
    } else {
        VPRINTF(LOW, "CLP_CORE: Error because there is no UDS prog request...\n");
        printf("%c",0xff); //End the test
    } 

}
