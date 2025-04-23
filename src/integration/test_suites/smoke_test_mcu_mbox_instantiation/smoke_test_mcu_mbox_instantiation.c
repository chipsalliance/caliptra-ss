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

// Test (in conjuction with Caliptra uC C code) tests in a side model with an MCU MBOX SRAM of 0 OKB  (tb_top_pkg.sv)
// In side build will also need to remove SRAM instantiation in caliptra_ss_tb_services.sv 
// 1. MCU will configure Caliptra uC to be a valid AXI
// 2. Caliptra uC will attempt CSR and SRAM read writes.  These are all expected to return AXI errors

void main (void) {
    int argc=0;
    char *argv[1];
    enum boot_fsm_state_e boot_fsm_ps;
    uint32_t mbox_resp_dlen;
    uint32_t mbox_resp_data;
    uint32_t mci_boot_fsm_go;
    uint32_t sram_data;  
    uint32_t mbox_num = decode_single_valid_mbox();
    bool     mbox0_sel = true;
    uint32_t axi_select = xorshift32() % 5;

    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };

    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Valid AXI USER for test AXI: 0x%x;\n", caliptra_uc_axi_id);

    if(mbox_num) {
        mbox0_sel = false;
    }

    mcu_cptra_init_d(.cfg_cptra_dma_axi_user=true, .cptra_dma_axi_user=caliptra_uc_axi_id, .cfg_mcu_mbox0_valid_user=mbox0_sel, .mcu_mbox0_valid_user=axi_user_id, .cfg_mcu_mbox1_valid_user=!mbox0_sel, .mcu_mbox1_valid_user=axi_user_id);

    // mcu_mbox_clear_lock_out_of_reset(mbox_num);

    ////////////////////////////////////
    // Mailbox command test
    ////////////////////////////////////


    VPRINTF(LOW, "MCU: Sequence complete\n");

    while(1);
}
