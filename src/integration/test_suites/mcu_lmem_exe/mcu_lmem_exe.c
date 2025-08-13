//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// 
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
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "veer-csr.h"
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

static const char* mcu_sram_msg __attribute__ ((section(".mcu_sram.msg"))) = "=================\nHello World from MCU SRAM\n=================\n";
static       uint32_t mcu_sram_array [8] __attribute__ ((section(".mcu_sram.array")));
void mcu_sram_print_msg (uint32_t decision) __attribute__ ((aligned(4),section (".mcu_sram.print_msg")));
void mcu_sram_do_nonsense (uint32_t decision) __attribute__ ((aligned(4),section (".mcu_sram.do_nonsense")));

void mcu_sram_print_msg (uint32_t decision) {
    uint32_t rg;
    // Execute some code in MCU SRAM
    // Use some non-determinism to avoid the compiler optimizing away this
    // function or inlining it.
    rg = lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_CONFIG0) ^ lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_CONFIG1);
    if (rg != 0) {
        VPRINTF(LOW, mcu_sram_msg);
    } else {
        printf("MCU: DECISION is %d\nMCU: MESSAGE is:\n%s", decision, mcu_sram_msg);
    }
    // LSU reads from MCU SRAM
    for (uint8_t ii = 0; ii < 8; ii++) {
        if ((mcu_sram_array[ii] & 0xf0000000) != (ii << 28)) {
            handle_error("Mismatch 0x%x\n",mcu_sram_array[ii]);
        }
    }
    return;
}

void mcu_sram_do_nonsense (uint32_t decision) {
    uint32_t rg;

    VPRINTF(LOW, "MCU: Executing nonsense from MCU SRAM (as cacheable)\n");
    rg = xorshift32() ^ xorshift32();
    rg ^= rg << 13;
    rg ^= rg >> 17;
    rg ^= rg <<  5;
    if (rg & 0x22110) {
        if (rg & decision) {
            VPRINTF(LOW, "MCU: rg has bits matching 0x%x AND 0x%x\n", 0x22110, decision);
        }
    }

    while(rg & decision) {
        rg >>= 1;
        VPRINTF(LOW, "  rg 0x%x\n", rg);
    }

    // LSU reads from MCU SRAM
    for (uint8_t ii = 0; ii < 8; ii++) {
        if ((mcu_sram_array[ii] & 0xf0000000) != (ii+8)<<28) {
            handle_error("Mismatch 0x%x\n",mcu_sram_array[ii]);
        }
    }

    return;
}

void main (void) {
    int argc=0;
    char *argv[1];
    uintptr_t addr;

    VPRINTF(LOW, "=================\nMCU: MCU SRAM Exec Test\n=================\n\n")

    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON) & MCI_REG_RESET_REASON_FW_BOOT_UPD_RESET_MASK) {
        uint32_t reg_val;

        // Perform some writes to MCU SRAM
        addr = (uintptr_t) (&mcu_sram_array) + 0 ; VPRINTF(LOW, "0x%x to 0x%x\n", 0x0a090807, addr); lsu_write_32(addr, 0x0a090807);
        addr = (uintptr_t) (&mcu_sram_array) + 4 ; VPRINTF(LOW, "0x%x to 0x%x\n", 0x1b1c1d1e, addr); lsu_write_32(addr, 0x1b1c1d1e);
        addr = (uintptr_t) (&mcu_sram_array) + 8 ; VPRINTF(LOW, "0x%x to 0x%x\n", 0x2a282921, addr); lsu_write_32(addr, 0x2a282921);
        addr = (uintptr_t) (&mcu_sram_array) + 12; VPRINTF(LOW, "0x%x to 0x%x\n", 0x3f3d3e33, addr); lsu_write_32(addr, 0x3f3d3e33);
        addr = (uintptr_t) (&mcu_sram_array) + 16; VPRINTF(LOW, "0x%x to 0x%x\n", 0x44454647, addr); lsu_write_32(addr, 0x44454647);
        addr = (uintptr_t) (&mcu_sram_array) + 20; VPRINTF(LOW, "0x%x to 0x%x\n", 0x5afecafe, addr); lsu_write_32(addr, 0x5afecafe);
        addr = (uintptr_t) (&mcu_sram_array) + 24; VPRINTF(LOW, "0x%x to 0x%x\n", 0x6adbabe5, addr); lsu_write_32(addr, 0x6adbabe5);
        addr = (uintptr_t) (&mcu_sram_array) + 28; VPRINTF(LOW, "0x%x to 0x%x\n", 0x7ee78008, addr); lsu_write_32(addr, 0x7ee78008);

        // Call a function located in MCU SRAM to show IFU accesses to MCU SRAM
        mcu_sram_print_msg(0xca5e);

        // Configure MCI as cacheable
        // MRAC
        //  - Set cacheable for MCI to test MCU SRAM caching
        reg_val = csr_read_mrac() & ~(MRAC_MCI_MASK);
        reg_val |= (0x1 << MRAC_MCI_LOW);
        csr_write_mrac_and_fence(reg_val);
        putchar('#');
        mcu_sleep(128);
        VPRINTF(LOW, "Set MCI as cacheable\n");
        
        // Perform some writes to MCU SRAM
        addr = (uintptr_t) (&mcu_sram_array) + 0 ; VPRINTF(LOW, "0x%x to 0x%x\n", 0x80000008, addr); lsu_write_32(addr, 0x80000008);
        addr = (uintptr_t) (&mcu_sram_array) + 4 ; VPRINTF(LOW, "0x%x to 0x%x\n", 0x9b9c9d9e, addr); lsu_write_32(addr, 0x9b9c9d9e);
        addr = (uintptr_t) (&mcu_sram_array) + 8 ; VPRINTF(LOW, "0x%x to 0x%x\n", 0xa2282921, addr); lsu_write_32(addr, 0xa2282921);
        addr = (uintptr_t) (&mcu_sram_array) + 12; VPRINTF(LOW, "0x%x to 0x%x\n", 0xb1b2b3b4, addr); lsu_write_32(addr, 0xb1b2b3b4);
        addr = (uintptr_t) (&mcu_sram_array) + 16; VPRINTF(LOW, "0x%x to 0x%x\n", 0xca5ec105, addr); lsu_write_32(addr, 0xca5ec105);
        addr = (uintptr_t) (&mcu_sram_array) + 20; VPRINTF(LOW, "0x%x to 0x%x\n", 0xdeadbeef, addr); lsu_write_32(addr, 0xdeadbeef);
        addr = (uintptr_t) (&mcu_sram_array) + 24; VPRINTF(LOW, "0x%x to 0x%x\n", 0xebaddabe, addr); lsu_write_32(addr, 0xebaddabe);
        addr = (uintptr_t) (&mcu_sram_array) + 28; VPRINTF(LOW, "0x%x to 0x%x\n", 0xface0ff0, addr); lsu_write_32(addr, 0xface0ff0);

        // Call a function located in MCU SRAM to show IFU accesses to MCU SRAM
        // when it's cacheable
        mcu_sram_do_nonsense(0xfee1);


        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
        while(1);
    } else {
        VPRINTF(LOW, "MCU: Bringing Caliptra out of Reset\n");
        mcu_cptra_init_d(.cfg_mcu_fw_sram_exec_reg_size=true, .mcu_fw_sram_exec_reg_size=0x8000);

        VPRINTF(LOW, "\nMCU: Wait for Caliptra reset req...\n");
        mcu_mci_poll_exec_lock();
        VPRINTF(LOW, "MCU: Observed Caliptra reset req; issuing reset\n\n");
        mcu_mci_req_reset();
        while(1);
    }
}
