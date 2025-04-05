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
#include "veer-csr.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main () {

    uint32_t ii;
    uint32_t data;

    // Message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra Bringup (in CSS)!!\n"    );
    VPRINTF(LOW, "----------------------------------\n");

    //set ready for FW as indication of life
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

    // Sleep
    for (uint16_t slp = 0; slp < 33; slp++);

    // Set FW EXEC REGION LOCK to enable MCU SRAM check
    VPRINTF(LOW, "FW: Setting FW_EXEC_CTRL\n");
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);

    // Wait for MCU test to finish and end sim
    // Halt the core
    __asm__ volatile ("csrwi    %0, %1" \
                : /* output: none */        \
                : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                : /* clobbers: none */);
}
