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
//
// ## LCC Register Test
//
// This test reads and writes all registers in the LCC.
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "riscv-csr.h"

#define MUBITRUE 0x96
#define MUBIFALSE 0x69

volatile uint32_t  rst_count = 0;
volatile uint32_t intr_count = 0;

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void nmi_handler (void) {
    VPRINTF(LOW, "*** Entering NMI Handler ***\n");
    if (csr_read_mcause() == (0xF0000000 + rst_count)) {
        intr_count += 1;
    }
    rst_count  += 1;
    SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);

}

void test_read_invalid_register(void) {
    VPRINTF(LOW, "============\nMCU: TESTING INVALID LCC REGISTER READ\n============\n\n");

    // Read outside LCC register space
    // This should trigger NMI
    lsu_read_32(SOC_LC_CTRL_MANUF_STATE_7 + 4);
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    VPRINTF(LOW, "============\nMCU: TESTING INVALID LCC REGISTER READ FINISHED\n============\n\n");
}

void test_write_invalid_register(void) {
    VPRINTF(LOW, "============\nMCU: TESTING INVALID LCC REGISTER WRITE\n============\n\n");

    lsu_write_32(SOC_LC_CTRL_MANUF_STATE_7 + 4, 0xdeadbeef);
    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    VPRINTF(LOW, "============\nMCU: TESTING INVALID LCC REGISTER WRITE FINISHED\n============\n\n");
}

void main (void) {
    VPRINTF(LOW, "=================\nMCU: Caliptra Boot Go\n=================\n\n");
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=true);
    lcc_initialization();
    VPRINTF(LOW, "==============\nMCU: TESTING LCC REGISTERS\n==============\n\n");
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR, (uint32_t) (nmi_handler));

    if (rst_count == 0) {
        test_write_invalid_register();
    } else if (rst_count == 1) {
        test_read_invalid_register();
    }

    for (uint8_t ii = 0; ii < 200; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (intr_count != 2) {
        SEND_STDOUT_CTRL(0x01);
    } else {
        SEND_STDOUT_CTRL(0xff);
    }
}
