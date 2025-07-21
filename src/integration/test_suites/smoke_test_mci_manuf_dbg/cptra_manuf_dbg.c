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
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"
#include "soc_address_map.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


/*
#### Debug Unlock
1. The ROM sets the `SS_DBG_MANUF_SERVICE_REG_RSP` register `MANUF_DBG_UNLOCK_IN_PROGRESS` bit to 1.

2. The ROM authorizes the debug unlock by setting the `SS_DBG_MANUF_SERVICE_REG_RSP` register `MANUF_DBG_UNLOCK_SUCCESS` bit to 1.

3. The ROM sets the `SS_DBG_MANUF_SERVICE_REG_RSP` register `MANUF_DBG_UNLOCK_IN_PROGRESS` bit to 0.
*/

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
    status_reg =  SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK;
    VPRINTF(LOW, "\n\nCLP_CORE: set MANUF_DBG_UNLOCK_SUCCESS is 0x%X...\n\n", status_reg);
    cpt_sleep(50000);
    

}
