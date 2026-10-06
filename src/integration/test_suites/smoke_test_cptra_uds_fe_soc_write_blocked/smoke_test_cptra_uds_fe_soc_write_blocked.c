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

// In subsystem mode, Caliptra core takes UDS/FE only from the fuse controller
// ports. The fuses are blank (ports are zero), the MCU writes non-zero UDS/FE
// over the bus before CPTRA_FUSE_WR_DONE, and the TB checks that Caliptra core
// still holds zeros.

#include <stdint.h>

#include "caliptra_ss_lib.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    VPRINTF(LOW, "=================\nMCU: Caliptra UDS/FE SoC write blocked test\n=================\n");

    mcu_mci_boot_go();
    mcu_cptra_wait_for_fuses();

    for (uint32_t dw = 0; dw < 16; dw++) {
        lsu_write_32(SOC_SOC_IFC_REG_FUSE_UDS_SEED_0 + 4 * dw, 0xA5A50000 | dw);
    }
    for (uint32_t dw = 0; dw < 8; dw++) {
        lsu_write_32(SOC_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0 + 4 * dw, 0x5A5A0000 | dw);
    }

    SEND_STDOUT_CTRL(CMD_EXPECT_CPTRA_UDS_FE_ZERO);
    mcu_sleep(100);

    mcu_cptra_set_fuse_done();
    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
