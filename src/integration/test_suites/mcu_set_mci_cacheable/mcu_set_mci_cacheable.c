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

#define MRAC_MCI_REGION (SOC_MCI_TOP_BASE_ADDR >> 28)
#define MRAC_MCI_LOW    (MRAC_MCI_REGION * 2)
#define MRAC_MCI_MASK   (0x3 << MRAC_MCI_LOW)

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
    //  - Set cacheable for MCI to test MCU SRAM caching
    reg_data = csr_read_mrac() & ~(MRAC_MCI_MASK);
    reg_data |= (0x1 << MRAC_MCI_LOW);
    csr_write_mrac_and_fence(reg_data);
    putchar('#'); // Print a unique character that shows up in waves to easily see when mrac is updated
    mcu_sleep(128);
    VPRINTF(LOW, "Set MCI as cacheable\n");

    // Initialize MCU mbox lock to 0
    // so we can detect if it gets erroneously acquired later
    mcu_mbox_clear_lock_out_of_reset(0);

    // Initialize MCU mbox lock to 0
    // so we can detect if it gets erroneously acquired later
    mcu_mbox_clear_lock_out_of_reset(0);

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

    // Try to read MCU MBOX USER register, then check if the LOCK was set as
    // as a side-effect
    VPRINTF(LOW, "MCU: Read MCU MBOX 0 USER\n");
    reg_data = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_USER);
    reg_data2 = lsu_read_32(SOC_MCI_TOP_MCU_MBOX0_CSR_MBOX_LOCK);
    if (reg_data2 & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK) {
        handle_error("Lock was acquired while reading from MBOX_USER, indicating some AXI misbehavior related to caching!\n");
    }

    // Try to write to MCU SRAM multiple times and read back the data
    reg_data = 0xfadebabe;
    reg_data2 = 0xba5eba11;

    VPRINTF(LOW, "MCU: Try writes to MCU SRAM\n");
    lsu_write_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1020, reg_data);
    lsu_write_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1044, reg_data2);

    if (lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1020) != reg_data) {
        handle_error("Data mismatch on MCU SRAM offset 0x%x. Data [0x%x] != Exp [0x%x]\n", 0x1020, lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1020), reg_data);
    }
    if (lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1044) != reg_data2) {
        handle_error("Data mismatch on MCU SRAM offset 0x%x. Data [0x%x] != Exp [0x%x]\n", 0x1044, lsu_read_32(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + 0x1044), reg_data2);
    }

    // return status is treated as an 'exit' code by mcu_crt0
    // 0-value indicates success, non-zero is error
    return 0;
}
