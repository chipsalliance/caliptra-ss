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
/*
    Run this test with the following command
    submit_i cpt_build2 -tc caliptra_ss_jtag_manuf_dbg -op -to 5000000
    or
    submit_i cpt_build -tc caliptra_ss_jtag_manuf_dbg -op -to 5000000
*/


#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void wait_for_mask(uint32_t addr, uint32_t mask)
{
    uint32_t seen = 0;
    do {
        seen = lsu_read_32(addr);
    } while (mask & ~seen);
}

void write_256(uint32_t base_address, const uint32_t vector[16])
{
    uint32_t addr = base_address;
    for (int i = 0; i < 16; i++, addr += 4) {
        VPRINTF(LOW, "MCU: writing 0x%x to 0x%x\n", vector[i], addr);
        lsu_write_32(addr, vector[i]);
    }
}

void main (void) {
    // New step: Writing the 16-word hash(MANUF_DBG_TOKEN) with byte swapping
    uint32_t vector[16] = {
        0xba03f195, 0xcfb86f60, 0x6ce5adc0, 0x90be97cd,
        0x5021e4df, 0x25edab7d, 0xb141e89a, 0xd115a87b,
        0x28abfbfa, 0x5a8f41, 0x44901cee, 0x4961df3f,
        0x8db3e5ea, 0x8d489c51, 0x90e26b42, 0xaf9369e
    };

    // Writing to Caliptra Boot GO register of MCI for CSS BootFSM to bring Caliptra out of reset
    // This is just to see CSSBootFSM running correctly
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 1);
    VPRINTF(LOW, "MCU: Writing MCI SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO\n");

    uint32_t cptra_boot_go = lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO);
    VPRINTF(LOW, "MCU: Reading SOC_MCI_TOP_MCI_REG_CALIPTRA_BOOT_GO %x\n", cptra_boot_go);

    ////////////////////////////////////
    // Fuse and Boot Bringup
    //
    // Wait for ready_for_fuses
    wait_for_mask(SOC_SOC_IFC_REG_CPTRA_FLOW_STATUS,
                  SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK);

    // Initialize fuses
    write_256(SOC_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0, vector);

    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_FUSE_WR_DONE, SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK);
    VPRINTF(LOW, "MCU: Set fuse wr done\n");

    mcu_sleep(5000);

    VPRINTF(LOW, "=================\n CALIPTRA_SS JTAG MANUF DEBUG FLOW TEST with ROM \n=================\n\n");

    mcu_sleep(5000);

    VPRINTF(LOW, "MCU: waits in success loop\n");
    wait_for_mask(SOC_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP,
                  SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK);

    mcu_sleep(5000);

    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
