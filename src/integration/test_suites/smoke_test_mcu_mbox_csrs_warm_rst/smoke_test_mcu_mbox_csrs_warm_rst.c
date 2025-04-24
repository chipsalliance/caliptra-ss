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

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


// Test will do a handful of random writes and read to the MCU SRAM including one at max size

void main (void) {
   
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t sram_data;  
    uint32_t mbox_num = decode_single_valid_mbox();
    bool     mbox0_sel = true;
    uint32_t axi_select = xorshift32() % 5;

    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };
    
    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Valid AXI USER for test AXI: 0x%x;\n", caliptra_uc_axi_id);

    VPRINTF(LOW, "=================\nMCU Warm Reset CSR Test\n=================\n\n")

    if(mbox_num) {
        mbox0_sel = false;
    }

    mcu_cptra_init_d(.cfg_cptra_dma_axi_user=true, .cptra_dma_axi_user=caliptra_uc_axi_id, .cfg_mcu_mbox0_valid_user=mbox0_sel, .mcu_mbox0_valid_user=axi_user_id, .cfg_mcu_mbox1_valid_user=!mbox0_sel, .mcu_mbox1_valid_user=axi_user_id);

    ////////////////////////////////////
    // MCU Warm Reset CSR Test
    ////////////////////////////////////

    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_RESET_REASON) & MCI_REG_RESET_REASON_WARM_RESET_MASK) {
        // If warm reset check CSR values are 0 (except for lock and MBOX USER)
        if((mcu_mbox_read_lock(mbox_num) & MCU_MBOX0_CSR_MBOX_LOCK_LOCK_MASK) == 0) {
            VPRINTF(FATAL, "MCU: Mbox%x lock should already be locked\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_mbox_user(mbox_num) == 0) {
            VPRINTF(FATAL, "MCU: Mbox%x mbox_user should be non-zero/MCU AXI\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_target_user(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x target_user should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_target_user_valid(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x target_user_valid should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_target_status(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x target_status should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_cmd(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x cmd should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_cmd_status(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x cmd_status should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_dlen(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x dlen should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_hw_status(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x mbox_hw_status should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        if(mcu_mbox_read_execute(mbox_num) != 0) {
            VPRINTF(FATAL, "MCU: Mbox%x execute should be zero\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        VPRINTF(LOW, "MCU: Sequence complete\n");
        SEND_STDOUT_CTRL(0xff);
    
        while(1);

    } else {
        // Write to CSRs and trigger warm reset
        mcu_mbox_write_dlen(mbox_num, xorshift32());
        mcu_mbox_write_cmd(mbox_num, xorshift32());
        mcu_mbox_write_cmd_status(mbox_num, 0xf);
        mcu_mbox_write_target_user(mbox_num, xorshift32());
        mcu_mbox_write_target_user_valid(mbox_num, 1);
        mcu_mbox_write_target_status(mbox_num, 0xffffffff);
        // Write to SRAM with single bit error
        SEND_STDOUT_CTRL(TB_CMD_INJECT_MBOX_SRAM_SINGLE_ECC_ERROR);

        uint32_t sram_size_kb = mcu_mbox_get_sram_size_kb(mbox_num);

        // Single write to SRAM (Due to timing, ECC injector won't inject error on first write)
        mcu_mbox_write_sram_dword(mbox_num, 0, 0);
    
        uint32_t rand_data = xorshift32();
        uint32_t rand_dword_addr = xorshift32() % (sram_size_kb * 256);
        mcu_mbox_write_sram_dword(mbox_num, rand_dword_addr, rand_data);
        uint32_t rd_data = mcu_mbox_read_sram_dword(mbox_num, rand_dword_addr);

        // Check that HW status is populated
        if (mcu_mbox_read_hw_status(mbox_num) & MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_SINGLE_ERROR_MASK) {
            VPRINTF(LOW, "MCU: Mbox%x SB ECC detected\n", mbox_num);
        } else {
            VPRINTF(FATAL, "MCU: Mbox%x No SB ECC detected\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Write to SRAM with double bit error
        SEND_STDOUT_CTRL(TB_CMD_DISABLE_MBOX_SRAM_ECC_ERROR_INJECTION);
        SEND_STDOUT_CTRL(TB_CMD_INJECT_MBOX_SRAM_DOUBLE_ECC_ERROR);

        // Single write to SRAM (Due to timing, ECC injector won't inject error on first write)
        mcu_mbox_write_sram_dword(mbox_num, 0, 0);
    
        rand_data = xorshift32();
        rand_dword_addr = xorshift32() % (sram_size_kb * 256);
        mcu_mbox_write_sram_dword(mbox_num, rand_dword_addr, rand_data);
        rd_data = mcu_mbox_read_sram_dword(mbox_num, rand_dword_addr);

        // Check that HW status is populated
        if (mcu_mbox_read_hw_status(mbox_num) & MCU_MBOX0_CSR_MBOX_HW_STATUS_ECC_DOUBLE_ERROR_MASK) {
            VPRINTF(LOW, "MCU: Mbox%x DB ECC detected\n", mbox_num);
        } else {
            VPRINTF(FATAL, "MCU: Mbox%x No DB ECC detected\n", mbox_num);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        SEND_STDOUT_CTRL(TB_CMD_DISABLE_MBOX_SRAM_ECC_ERROR_INJECTION);
        mcu_mbox_set_execute(mbox_num);

        // Initiate warm_reset
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);

        while(1);
    }
}
