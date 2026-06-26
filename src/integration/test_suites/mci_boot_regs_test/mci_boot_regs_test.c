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

#include "mci.h"
#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "veer-csr.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {

    VPRINTF(LOW, "==================\nMCI BOOTFSM_GO and CPTRA_BOOT_GO Registers Access Test\n==================\n\n");

    // MCU is running so accessing BOOTFSM_GO reg shouldn't cuase issue
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO, MCI_REG_MCI_BOOTFSM_GO_GO_MASK);
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO) != MCI_REG_MCI_BOOTFSM_GO_GO_MASK) {
        VPRINTF(LOW, "Incorrect SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO expected:%x, got: %x\n",
            MCI_REG_MCI_BOOTFSM_GO_GO_MASK, lsu_read_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO));
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
    // Access adjacent byte in the same register
    lsu_write_8(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO + 1, 0);
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO) != MCI_REG_MCI_BOOTFSM_GO_GO_MASK) {
        VPRINTF(LOW, "Incorrect SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO expected:%x, got: %x\n",
            MCI_REG_MCI_BOOTFSM_GO_GO_MASK, lsu_read_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO));
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
    lsu_write_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO, 0);
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO) != 0) {
        VPRINTF(LOW, "Incorrect SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO expected: 0, got: %x\n",
            lsu_read_32(SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO));
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, MCI_REG_CPTRA_BOOT_GO_GO_MASK);
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO) != MCI_REG_CPTRA_BOOT_GO_GO_MASK) {
        VPRINTF(LOW, "Incorrect SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO expected:%x, got: %x\n",
            MCI_REG_CPTRA_BOOT_GO_GO_MASK, lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO));
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
    // Access adjacent byte in the same register
    lsu_write_8(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO + 1, 0);
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO) != MCI_REG_CPTRA_BOOT_GO_GO_MASK) {
        VPRINTF(LOW, "Incorrect SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO expected:%x, got: %x\n",
            MCI_REG_CPTRA_BOOT_GO_GO_MASK, lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO));
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
    lsu_write_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, 0);
    if (lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO) != 0) {
        VPRINTF(LOW, "Incorrect SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO expected: 0, got: %x\n",
            lsu_read_32(SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO));
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
}
