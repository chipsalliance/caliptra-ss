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
//
// Test: mci_lcc_no_zeroization
//
// Verifies that zeroization does NOT trigger when PPD stays 0, regardless of
// the ss_soc_MCU_ROM_zeroization_mask_reg value (FC_FIPS_ZEROZATION register).
//
// FIPS_ZEROIZATION_CMD_o = (&ss_soc_MCU_ROM_zeroization_mask_reg) & FIPS_ZEROIZATION_PPD_i
//
// With PPD=0, the AND result is 0 in both paths tested:
//   FIPS-mask path: random non-zero value written to FC_FIPS_ZEROZATION, PPD=0
//   PPD path:       zero written to FC_FIPS_ZEROZATION, PPD=0
// The path is selected randomly each run via xorshift32.
// The test confirms this by verifying debug_locked remains 0 after the write.
//
//********************************************************************************
#include <stdint.h>

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    VPRINTF(LOW, "=================\nMCU mci_lcc_no_zeroization\n=================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);

    lcc_initialization();
    grant_mcu_for_fc_writes();

    transition_state_check(TEST_UNLOCKED0, raw_unlock_token);

    initialize_otp_controller();

    // Confirm OTP broadcast is valid before the test: debug_locked should be 0.
    uint32_t sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    if (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) {
        VPRINTF(LOW, "ERROR: expected debug_locked=0 before zeroization mask write, got SECURITY_STATE=0x%08x\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: debug_locked=0 confirmed before test (SECURITY_STATE=0x%08x)\n", sec_state);

    // Randomly choose between two no-zeroization paths (PPD is always 0 in testbench).
    // FIPS_ZEROIZATION_CMD_o = mask & PPD_i - with PPD=0 the result is 0 in both cases.
    uint32_t rand_val = xorshift32();
    uint32_t mask_val;
    const char *path_name;
    if (rand_val & 1) {
        // FIPS-mask path: all 1s mask, PPD=0 -> cmd=0
        mask_val = 0xffffffff;
        path_name = "FIPS mask";
    } else {
        // PPD path: mask=0, PPD=1 -> cmd=0 regardless of mask
        mask_val = 0x0;
        path_name = "PPD (mask=1)";
    }
    VPRINTF(LOW, "INFO: writing 0x%08x to FC_FIPS_ZEROZATION (%s path)\n", mask_val, path_name);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FC_FIPS_ZEROZATION, mask_val);
    if (mask_val == 0) {
        lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_FC_FORCE_PPD);
    }

    // Allow a few cycles for any unintended side-effects to propagate.
    for (uint8_t i = 0; i < 32; i++) {
        __asm__ volatile ("nop");
    }

    // Verify the register was written correctly.
    uint32_t mask_rb = lsu_read_32(SOC_MCI_TOP_MCI_REG_FC_FIPS_ZEROZATION);
    if (mask_rb != mask_val) {
        VPRINTF(LOW, "ERROR: FC_FIPS_ZEROZATION readback 0x%08x, expected 0x%08x\n", mask_rb, mask_val);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: FC_FIPS_ZEROZATION reads back 0x%08x as expected\n", mask_rb);

    // Verify that OTP was NOT zeroized: debug_locked must still be 0.
    sec_state = lsu_read_32(SOC_MCI_TOP_MCI_REG_SECURITY_STATE);
    if (sec_state & MCI_REG_SECURITY_STATE_DEBUG_LOCKED_MASK) {
        VPRINTF(LOW, "ERROR: debug_locked=1 after mask-only write - unexpected zeroization! SECURITY_STATE=0x%08x\n", sec_state);
        SEND_STDOUT_CTRL(0x01);
        return;
    }
    VPRINTF(LOW, "INFO: debug_locked=0 confirmed - OTP was NOT zeroized as expected (SECURITY_STATE=0x%08x)\n", sec_state);

    // Clean up: clear the mask register.
    lsu_write_32(SOC_MCI_TOP_MCI_REG_FC_FIPS_ZEROZATION, 0x0);
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT, CMD_RELEASE_PPD);

    for (uint8_t i = 0; i < 160; i++) {
        __asm__ volatile ("nop");
    }

    SEND_STDOUT_CTRL(0xff);
}
