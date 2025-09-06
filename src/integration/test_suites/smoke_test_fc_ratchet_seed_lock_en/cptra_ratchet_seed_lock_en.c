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
//
#include "caliptra_defines.h"
#include "printf.h"
#include "riscv-csr.h"
#include "soc_ifc.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "caliptra_isr.h"
#include "soc_address_map.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile caliptra_intr_received_s cptra_intr_rcv = {0};
const uint32_t testData[] = {0xA5A5A5A5, 0x96969696};

static inline void sleep (const uint32_t cycles) {
    for (uint8_t ii = 0; ii < cycles; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

void check_ratched_seeds() {
    uint32_t base_address = CLP_SOC_IFC_REG_FUSE_HEK_SEED_3;
    for (uint32_t i=0;i<2;i++){
        uint32_t data = lsu_read_32(base_address + i*4);
        if (data != testData[0]) {
            VPRINTF(LOW, "CLP_CORE ERROR: HEK read failed at index %d: expected %08X, got 0x%08X \n", i, testData, data);
            return;
        }
    }
}


void main(void) {
    VPRINTF(LOW,"----------------------------------\nCaliptra: Mimicking ROM from Subsystem!!\n----------------------------------\n");

    check_ratched_seeds();

    uint32_t status_reg = SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK;
    lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, status_reg);
    VPRINTF(LOW, "CLP_CORE: \n\nSet OCP_LOCK_CTRL_LOCK_IN_PROGRESS high 0x%X...\n\n", status_reg);
    
    sleep(50000);
}
