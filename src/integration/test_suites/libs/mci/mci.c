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
//

#include "mci.h"
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "string.h"
#include "stdint.h"
#include <stdbool.h>

uint32_t get_mcu_sram_size(){
    return (lsu_read_32(SOC_MCI_TOP_MCI_REG_HW_CONFIG1)  & MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_MASK) >> MCI_REG_HW_CONFIG1_MCU_SRAM_SIZE_LOW;
}

uint32_t get_mcu_sram_size_byte(){
    return get_mcu_sram_size() * 1024;
}

uint32_t get_mcu_sram_end_addr(){
   return SOC_MCI_TOP_MCU_SRAM_BASE_ADDR + get_mcu_sram_size_byte() - 1;

}

uint32_t get_mcu_sram_last_dword(){
    return get_mcu_sram_end_addr() & ~3;
}

uint32_t get_mcu_sram_execution_region_start() {
    return SOC_MCI_TOP_MCU_SRAM_BASE_ADDR;
}

uint32_t get_mcu_sram_execution_region_end() {
    uint32_t fw_exec_region;

    fw_exec_region = lsu_read_32(SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE) + 1; // BASE 0 so add 1 for any calculations
    
    return get_mcu_sram_execution_region_start() + (fw_exec_region * 4 * 1024) -1;

}

uint32_t get_fw_sram_exec_region_less_than_sram_size(uint32_t rnd){
    uint32_t mask_rnd = rnd & MCI_REG_FW_SRAM_EXEC_REGION_SIZE_SIZE_MASK;
    uint32_t sram_size = get_mcu_sram_size();
    uint32_t fw_sram_exec_region = (mask_rnd % sram_size) >> 4;
    return fw_sram_exec_region;
}

bool get_is_sram_protected_region(){
    return get_mcu_sram_protected_region_start() <= get_mcu_sram_end_addr();
}

uint32_t get_mcu_sram_protected_region_start() {
    return get_mcu_sram_execution_region_end() + 1;
}

uint32_t get_mcu_sram_protected_region_end() {
   return get_mcu_sram_end_addr();

}

