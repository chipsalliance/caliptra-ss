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
// Debug-intent background integrity/consistency check test.
//
// All secret partitions are provisioned and locked in the VMEM (see
// secret_partitions_locked.hjson) and the debug-intent strap is asserted
// (+CALIPTRA_SS_DEBUG_INTENT). Under debug intent:
//   - The manuf/prod/vendor secret partitions are debug-zeroized: they ACK
//     background checks without executing them, so they never fail.
//   - SECRET_LC_TRANSITION_PARTITION is EXCLUDED from zeroization so LCC can
//     transition, so it runs REAL integrity/consistency checks using the real
//     scrambler key.
//
// This test enables both background checks with a very small period and lets the
// fuse controller run many check rounds. It verifies that none of these checks
// fail (no OTP STATUS error bits and no FC fatal alert) while debug intent is high.

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "caliptra_ss_lc_ctrl_address_map.h"
#include "caliptra_ss_lib.h"
#include "fuse_ctrl.h"
#include "lc_ctrl.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_address_map.h"
#include "soc_ifc.h"

volatile char *stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

// Run a few back-to-back background check rounds. The sleep spans ~2x the 0x40
// integrity/consistency period (~16.6K cycles max) so a fresh integrity+consistency
// round genuinely elapses between polls rather than the loop spinning on an
// already-idle controller.
#define CHECK_POLL_ROUNDS   3u
#define CHECK_POLL_SLEEP    8000u

static void check_ss_debug_intent_high(void) {
    uint32_t debug_intent = lsu_read_32(SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT);
    if ((debug_intent & MCI_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK) == 0) {
        handle_error("ERROR: SS_DEBUG_INTENT bit0 is not high\n");
    }
}

static void enable_background_checks(void) {
    // Generous timeout so a legitimate full-partition check always completes in time.
    lsu_write_32(SOC_OTP_CTRL_CHECK_TIMEOUT, 0x00100000);

    // Very small (but non-zero) periods so integrity and consistency checks are
    // triggered back-to-back. A zero mask would disable the check entirely.
    lsu_write_32(SOC_OTP_CTRL_INTEGRITY_CHECK_PERIOD, 0x00000040);
    lsu_write_32(SOC_OTP_CTRL_CONSISTENCY_CHECK_PERIOD, 0x00000040);

    // Lock the background-check configuration so it cannot be disturbed.
    lsu_write_32(SOC_OTP_CTRL_CHECK_REGWEN, 0x0);

    VPRINTF(LOW, "INFO: background checks enabled (period=0x40, timeout=0x100000)\n");
}

void main(void) {
    VPRINTF(LOW, "==========================================\n"
                 "MCU debug-intent integrity check test\n"
                 "==========================================\n\n");

    mcu_cptra_init_d();
    wait_dai_op_idle(0);
    lcc_initialization();

    check_ss_debug_intent_high();

    // Confirm the controller initialized cleanly before enabling background checks.
    if (!wait_dai_op_idle(0)) {
        handle_error("ERROR: fuse controller reported an error before enabling checks\n");
    }

    enable_background_checks();

    // Run 3 back-to-back integrity/consistency rounds and confirm none of them fail
    // while debug intent is asserted. A failed check latches an error bit in
    // OTP_CTRL_STATUS (and a partition error), which wait_dai_op_idle(0) would flag.
    for (uint32_t i = 0; i < CHECK_POLL_ROUNDS; i++) {
        mcu_sleep(CHECK_POLL_SLEEP);
        if (!wait_dai_op_idle(0)) {
            handle_error("ERROR: background integrity/consistency check failed under debug intent\n");
        }
    }

    VPRINTF(LOW, "INFO: background checks passed under debug intent\n");

    SEND_STDOUT_CTRL(0xff);
}
