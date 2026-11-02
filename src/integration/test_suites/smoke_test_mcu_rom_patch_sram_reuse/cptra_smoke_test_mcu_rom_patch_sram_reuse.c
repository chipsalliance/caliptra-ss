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
// MCU ROM patch SRAM reuse test, Caliptra core side: hand off to MCU RT FW.
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "soc_address_map.h"
#include <stdint.h>
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main(void) {
    uint64_t mci_base_addr;
    uint32_t data;

    VPRINTF(LOW, "Caliptra: Handing off to MCU RT FW\n");
    mci_base_addr = ((uint64_t) lsu_read_32(CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_L)) |
                    ((uint64_t) lsu_read_32(CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_H) << 32);
    data = MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK;
    soc_ifc_axi_dma_send_ahb_payload(mci_base_addr + MCI_REG_RESET_REASON, 0, &data, 4, 0);
    lsu_write_32(CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0, 0x4);

    // Halt the core
    __asm__ volatile ("csrwi    %0, %1" \
                : /* output: none */        \
                : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                : /* clobbers: none */);
}
