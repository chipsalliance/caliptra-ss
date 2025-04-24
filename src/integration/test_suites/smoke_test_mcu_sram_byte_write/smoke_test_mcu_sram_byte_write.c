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
#include <string.h>
#include <stdint.h>

#define KB 1024

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {
    uint32_t mcu_protected_region_start = get_mcu_sram_protected_region_start();
    uint32_t mcu_protected_region_end = get_mcu_sram_last_dword(); // Default size


    VPRINTF(LOW, "=================\nByte tesing to MCU SRAM\n=================\n\n");
    VPRINTF(LOW, "==\nByte Writes start of protected region\n==\n");
    VPRINTF(LOW, "Start Protected region: 0x%x\n", mcu_protected_region_start);
    lsu_write_32(mcu_protected_region_start, 0x0);
    read_check(mcu_protected_region_start, 0x0); 

    lsu_write_8(mcu_protected_region_start, 0xFF);
    read_check(mcu_protected_region_start, 0xFF);

    lsu_write_8(mcu_protected_region_start + 0x1, 0xFF);
    read_check(mcu_protected_region_start, 0xFFFF);

    lsu_write_8(mcu_protected_region_start + 0x2, 0xFF);
    read_check(mcu_protected_region_start, 0xFFFFFF); 

    lsu_write_8(mcu_protected_region_start + 0x3, 0xFF);
    read_check(mcu_protected_region_start, 0xFFFFFFFF);

    lsu_write_8(mcu_protected_region_start, 0x00);
    read_check(mcu_protected_region_start, 0xFFFFFF00);

    lsu_write_8(mcu_protected_region_start + 0x1, 0x00);
    read_check(mcu_protected_region_start, 0xFFFF0000);

    lsu_write_8(mcu_protected_region_start + 0x2, 0x00);
    read_check(mcu_protected_region_start, 0xFF000000);

    lsu_write_8(mcu_protected_region_start + 0x3, 0x00);
    read_check(mcu_protected_region_start, 0x00);

    VPRINTF(LOW, "==\nByte Writes end of protected region\n==\n");
    lsu_write_32(mcu_protected_region_end, 0x0);
    read_check(mcu_protected_region_end, 0x0);

    lsu_write_8(mcu_protected_region_end, 0xFF);
    read_check(mcu_protected_region_end, 0xFF);

    lsu_write_8(mcu_protected_region_end + 0x1, 0xFF);
    read_check(mcu_protected_region_end, 0xFFFF);

    lsu_write_8(mcu_protected_region_end + 0x2, 0xFF);
    read_check(mcu_protected_region_end, 0xFFFFFF);

    lsu_write_8(mcu_protected_region_end + 0x3, 0xFF);
    read_check(mcu_protected_region_end, 0xFFFFFFFF);

    lsu_write_8(mcu_protected_region_end, 0x00);
    read_check(mcu_protected_region_end, 0xFFFFFF00);

    lsu_write_8(mcu_protected_region_end + 0x1, 0x00);
    read_check(mcu_protected_region_end, 0xFFFF0000);

    lsu_write_8(mcu_protected_region_end + 0x2, 0x00);
    read_check(mcu_protected_region_end, 0xFF000000);

    lsu_write_8(mcu_protected_region_end + 0x3, 0x00);
    read_check(mcu_protected_region_end, 0x00);

    SEND_STDOUT_CTRL(0xff);

}
