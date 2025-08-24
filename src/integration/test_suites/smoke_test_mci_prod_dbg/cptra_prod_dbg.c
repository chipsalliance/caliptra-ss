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


#define exp_mbox_cmd                0x4d445554
#define MBOX_DLEN_VAL               9 // This plus 4 is for checksum
uint32_t read_TOKEN[9];
uint32_t exp_token[9] = {
    0xFFFFF8E2,
    0xABCDEFEB,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0x00000000,
    0xF888888A
};


/*
#### Debug Unlock
1. ROM sets the `SS_DBG_SERVICE_REG_RSP` register `PROD_DBG_UNLOCK_IN_PROGRESS` bit to 1.

2. The ROM authorizes the debug unlock by setting the `SS_DBG_SERVICE_REG_RSP` register `PROD_DBG_UNLOCK_SUCCESS` bit to 1.

3. Just for testing purposes, the ROM sets the UNLOCK_LEVEL registers to 0xFFFFFFFF.

4. The ROM sets the `SS_DBG_SERVICE_REG_RSP` register `PROD_DBG_UNLOCK_IN_PROGRESS` bit to 0.
*/


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

void main(void) {
    int argc=0;
    char *argv[1];

    VPRINTF(LOW,"----------------------------------\nCaliptra: Mimicking ROM from Subsystem!!\n----------------------------------\n");
    uint32_t status_reg ;
    status_reg =  SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK;
    VPRINTF(LOW, "CLP_CORE: set PROD_DBG_UNLOCK_IN_PROGRESS...\n");
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
    status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP);
    status_reg = status_reg | SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK;
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
    VPRINTF(LOW, "\n\nCLP_CORE: set PROD_DBG_UNLOCK_SUCCESS high 0x%X...\n\n", status_reg);
    status_reg = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP);
    status_reg = 0xFFFFFFFF;
    lsu_write_32(CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0, status_reg);
    lsu_write_32(CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1, status_reg);
    VPRINTF(LOW, "\n\nCLP_CORE: CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL is 0x%X%X..\n\n", status_reg, status_reg);
    status_reg = status_reg & (SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK ^ 0xFFFFFFFF);
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, status_reg);
    VPRINTF(LOW, "CLP_CORE: set low to PROD_DBG_UNLOCK_IN_PROGRESS...\n");
    cpt_sleep(50000);

}
