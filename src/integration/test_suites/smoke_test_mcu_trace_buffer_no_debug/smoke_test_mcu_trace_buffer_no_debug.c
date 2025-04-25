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
#include "mci.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "lc_ctrl.h"
#include <string.h>
#include <stdint.h>


volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {
    uint32_t mcu_protected_region_start;
    uint32_t mcu_protected_region_end; 
    uint32_t mcu_protected_region_real_end;
    uint32_t rnd = xorshift32();
    uint32_t rnd_shift = rnd % 32;
    uint32_t rnd_num_writes = rnd % 64;
    uintptr_t address;
    // Get a protected region that doesn't exceed the size of the SRAM
    uint32_t rnd_protected_region_size = get_fw_sram_exec_region_less_than_sram_size(rnd);
    // Enable Caliptra MBOX access
    uint32_t axi_select = xorshift32() % 5;
    uint32_t axi_user_id[] = { xorshift32(), xorshift32(), xorshift32(), xorshift32(), xorshift32() };
    uint32_t caliptra_uc_axi_id = axi_user_id[axi_select];
    VPRINTF(LOW, "MCU: Valid AXI USER for test AXI: 0x%x;\n", caliptra_uc_axi_id);

    mcu_mbox_clear_lock_out_of_reset(0);

    VPRINTF(LOW, "=================\nMCU: Testing MCU trace buffer\n=================\n\n");
    
    VPRINTF(LOW, "MCU: Configuring MCU MBOX\n");
    mcu_mbox_configure_valid_axi(0, axi_user_id); 
    


    mcu_protected_region_start = get_mcu_sram_protected_region_start();
    mcu_protected_region_end = get_mcu_sram_last_dword(); // Default size
    mcu_protected_region_real_end = get_mcu_sram_protected_region_end();

    VPRINTF(LOW, "MCU: Start Protected region: 0x%x\n", mcu_protected_region_start);
    VPRINTF(LOW, "MCU: End Protected region: 0x%x\n", mcu_protected_region_real_end);
    VPRINTF(LOW, "MCU: End DWORD Protected region: 0x%x\n", mcu_protected_region_end);
    VPRINTF(LOW, "MCU: Is there a Protected region? 0x%x\n", get_is_sram_protected_region());
    
    VPRINTF(LOW, "MCU: Writing start of protected region 0x%x with 0x%x\n", mcu_protected_region_start, rnd);
    write_read_check(mcu_protected_region_start, rnd);


    rnd ^= rnd << rnd_shift; 
    VPRINTF(LOW, "MCU: Writing end of protected region 0x%x with 0x%x\n", mcu_protected_region_end, rnd);
    write_read_check(mcu_protected_region_end, rnd);

    // Loop forever until the TB stops the test
    while(1) {
        rnd = xorshift32();
        VPRINTF(LOW, "MCU: Writing %d random addresses in MCU SRAM\n", rnd_num_writes);
        for(int i = 0; i < rnd_num_writes; i++) {
            address = get_random_address(rnd + i*4, mcu_protected_region_start, mcu_protected_region_real_end);
            VPRINTF(LOW, "MCU: Random Write Address 0x%x: 0x%x\n", address, rnd + i);
            lsu_write_32(address, rnd + i);
        }
        VPRINTF(LOW, "MCU: Checking Writing %d random addresses in MCU SRAM\n", rnd_num_writes);
        for(int i = 0; i < rnd_num_writes; i++) {
            address = get_random_address(rnd + i*4, mcu_protected_region_start, mcu_protected_region_real_end);
            read_check(address, rnd + i);
        }
    }

}
