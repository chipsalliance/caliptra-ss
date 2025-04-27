//********************************************************************************
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
//********************************************************************************

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "veer-csr.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdint.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t main (void) {
    int argc=0;
    char *argv[1];
    uint32_t reg_data, reg_data2;

    VPRINTF(LOW, "=================\nMCU: Cacheable MCI Test\n=================\n\n")

    // Configure MCI as cacheable
    // MRAC
    // Disable Caches on all regions except...
    //  - Set cacheable for ROM to improve perf
    //  - Set cacheable for MCI to test MCU SRAM caching
    // Set side-effects (SE) at peripheral address regions:
    //  - [UNMAPPED] @ 0x0000_0000:    SE
    //  - [UNMAPPED] @ 0x1000_0000:    SE
    //  - MCI/I3C    @ 0x2000_0000: no SE, +Cache
    //  - [UNMAPPED] @ 0x3000_0000:    SE
    //  - [UNMAPPED] @ 0x4000_0000:    SE
    //  - DCCM       @ 0x5000_0000: no SE
    //  - PIC        @ 0x6000_0000:    SE
    //  - FC/LCC     @ 0x7000_0000:    SE
    //  - imem       @ 0x8000_0000: no SE, +Cache
    //  - [UNMAPPED] @ 0x9000_0000:    SE
    //  - soc_ifc    @ 0xA000_0000:    SE
    //  - ...
    //  - [UNMAPPED] @ 0xC000_0000:    SE
    //  - [UNMAPPED] @ 0xD000_0000:    SE
    //  - [UNMAPPED] @ 0xE000_0000:    SE
    //  - [UNMAPPED] @ 0xF000_0000:    SE
    csr_write_mrac_and_fence(0xAAA9A29A);

    // Test if MCI regs are cached by repeatedly reading MTIME
    for (uint32_t ii = 0; ii < 32; ii++) {
        reg_data = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L);
        VPRINTF(LOW, "MCU: MTIME_L:              0x%x\n", reg_data);
        mcu_sleep(64);
        reg_data2 = lsu_read_32(SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L);
        if (reg_data == reg_data2) {
            handle_error("Timer didn't increment! %x %x\n", reg_data, reg_data2);
        } else if (reg_data > reg_data2) {
            handle_error("Timer unexpectedly decremented! %x %x\n", reg_data, reg_data2);
        } else {
            VPRINTF(LOW, "     MTIME_L (after wait): 0x%x\n", reg_data2);
        }
    }

    // return status is treated as an 'exit' code by mcu_crt0
    // 0-value indicates success, non-zero is error
    return 0;
}
