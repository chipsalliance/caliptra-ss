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

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main (void) {
    int argc=0;
    char *argv[1];
    uint32_t reg_data;
    uint32_t sram_data;

    VPRINTF(LOW, "=================\nMCU: Subsytem Bringup\n=================\n\n")
    VPRINTF(LOW, "MCU: Load SHA vector to MCU SRAM for testing\n")
    SEND_STDOUT_CTRL(TB_CMD_SHA_VECTOR_TO_MCU_SRAM);

    VPRINTF(LOW, "MCU: Caliptra bringup\n")

    mcu_cptra_init_d(.mcu_fw_sram_exec_reg_size=32, .cfg_mcu_fw_sram_exec_reg_size=true); // Set to 128KB 

    //Halt the core to wait for Caliptra to finish the test
    csr_write_mpmc_halt();

}
