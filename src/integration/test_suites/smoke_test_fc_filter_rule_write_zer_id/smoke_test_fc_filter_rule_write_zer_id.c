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
// Coverage targets: fuse_ctrl_filter.sv — uncovered FSM paths
//
// This test exercises four uncovered paths in the fuse_ctrl_filter FSM:
//
//   Scenario 1: trigger_table_check branch in FUSE_ADDR_AXI_WR_ST state.
//       Writing DIRECT_ACCESS_ADDRESS twice in a row so the FSM sees
//       trigger_table_check while already in FUSE_ADDR_AXI_WR_ST.
//
//   Scenario 2: DaiWrite with !wr_req_allowed in FUSE_CMD_AXI_ADDR_ST state.
//       Issuing a DaiWrite from the MCU user to a secret partition address,
//       causing !wr_req_allowed and a discard.
//
//   Scenario 3: DaiWrite with !all_same_id in FUSE_CMD_AXI_ADDR_ST state.
//       Issuing a DaiWrite where WDATA registers are written with MCU user
//       but ADDRESS+CMD use Caliptra core user, causing !all_same_id and
//       a discard.
//
//   Scenario 4: DaiZeroize with !addr_and_cmd_same_id in FUSE_CMD_AXI_ADDR_ST
//       state. Issuing a DaiZeroize where ADDRESS is written with MCU user
//       but CMD uses Caliptra core user, causing !addr_and_cmd_same_id and
//       a discard.
//
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
#include "fuse_ctrl_mmap.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

//----------------------------------------------------------------------------
// Scenario 1: Double ADDRESS write — trigger_table_check in FUSE_ADDR_AXI_WR_ST
//
// Normal DAI operations write DIRECT_ACCESS_ADDRESS exactly once before
// writing DIRECT_ACCESS_CMD. By writing ADDRESS twice in a row, the first
// write takes the FSM through:
//   IDLE_ST -> (trigger_table_check) -> FUSE_ADDR_AXI_ADDR_ST
//           -> (write_event)         -> FUSE_ADDR_AXI_WR_ST
// The second ADDRESS write fires trigger_table_check *while the FSM is in
// FUSE_ADDR_AXI_WR_ST*, which is the uncovered branch. The FSM gracefully
// loops back to FUSE_ADDR_AXI_ADDR_ST and re-latches addr_id with the new
// address.
//
// After the double-address write, we issue a normal DaiRead command so the
// FSM completes and returns to IDLE_ST.
//----------------------------------------------------------------------------
bool test_double_address_write(void) {
    VPRINTF(LOW, "\n--- Scenario 1: trigger_table_check in FUSE_ADDR_AXI_WR_ST ---\n");

    // Use Caliptra core identity so the final DaiRead is allowed for any address.
    grant_caliptra_core_for_fc_writes();
    mcu_sleep(20);
    if (!wait_dai_op_idle(0)) return false;

    const partition_t uds = partitions[SECRET_MANUF_PARTITION];
    const partition_t fe0 = partitions[SECRET_PROD_PARTITION_0];

    // First ADDRESS write: moves FSM from IDLE_ST to FUSE_ADDR_AXI_WR_ST.
    VPRINTF(LOW, "DEBUG: Writing first address 0x%08X\n", uds.address);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, uds.address);

    // Second ADDRESS write: hits trigger_table_check in FUSE_ADDR_AXI_WR_ST,
    // re-latches addr_id and goes back to FUSE_ADDR_AXI_ADDR_ST.
    VPRINTF(LOW, "DEBUG: Writing second address 0x%08X (trigger_table_check in FUSE_ADDR_AXI_WR_ST)\n", fe0.address);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, fe0.address);

    // Issue DaiRead command to complete the transaction and return FSM to IDLE.
    // This is needed so the FSM doesn't stay stuck waiting for a command.
    VPRINTF(LOW, "DEBUG: Completing with DaiRead command\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, 0x1);

    // The DaiRead should complete without error since Caliptra core is authorized.
    if (!wait_dai_op_idle(0)) return false;

    VPRINTF(LOW, "PASS: Scenario 1 completed\n");
    return true;
}

//----------------------------------------------------------------------------
// Scenario 2: Unauthorized DaiWrite — DaiWrite + !wr_req_allowed in
// FUSE_CMD_AXI_ADDR_ST
//
// The access_control_table in otp_ctrl_pkg.sv grants the MCU user access
// to ranges [0x00,0x40] and [0xF8,0x3FD8], but NOT the secret range
// [0x48,0xF0] (SECRET_MANUF through SECRET_PROD_3). Only Caliptra core
// (entry[0]) covers the full range [0x00,0x3FD8].
//
// By revoking the Caliptra core grant (reverting to MCU's native awuser)
// and issuing a dai_wr() to the SECRET_MANUF_PARTITION (address 0x48),
// the filter reaches FUSE_CMD_AXI_ADDR_ST with:
//   - fuse_cmd = DaiWrite
//   - latched_cmd_id = MCU user
//   - latched_fuse_addr = 0x48 (secret range)
//   - wr_req_allowed = false (MCU not in table for [0x48,0xF0])
//
// Earlier branches in FUSE_CMD_AXI_ADDR_ST are skipped:
//   - DaiRead branch: fuse_cmd is DaiWrite, not DaiRead
//   - DaiWrite debug+secret branch: cptra_in_debug_mode_i is 0 (default)
// So the DaiWrite + !wr_req_allowed condition fires: discard_fuse_write = 1.
//
// We use the existing dai_wr() library function which writes WDATA_0,
// WDATA_1, ADDRESS, CMD in standard order and then polls STATUS.
//----------------------------------------------------------------------------
bool test_unauthorized_dai_write(void) {
    VPRINTF(LOW, "\n--- Scenario 2: DaiWrite + !wr_req_allowed in FUSE_CMD_AXI_ADDR_ST ---\n");

    // Revoke Caliptra core grant so the MCU's native awuser is used.
    // MCU user is NOT authorized for the secret address range.
    revoke_grant_mcu_for_fc_writes();
    mcu_sleep(20);
    if (!wait_dai_op_idle(0)) return false;

    const partition_t uds = partitions[SECRET_MANUF_PARTITION];

    // Attempt a standard DaiWrite to the secret UDS partition with MCU user.
    // The filter will discard this because wr_req_allowed is false for MCU
    // at address 0x48. We expect OTP_CTRL_STATUS_DAI_ERROR_MASK in status.
    VPRINTF(LOW, "DEBUG: Attempting DaiWrite to secret addr 0x%08X with MCU user\n", uds.address);
    if (!dai_wr(uds.address, 0xA5A5A5A5, 0x5A5A5A5A, uds.granularity,
                OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
        VPRINTF(LOW, "ERROR: Unexpected status from unauthorized DaiWrite\n");
        return false;
    }

    VPRINTF(LOW, "PASS: Scenario 2 completed - DaiWrite correctly discarded\n");
    return true;
}

//----------------------------------------------------------------------------
// Scenario 3: DaiWrite with mixed AXI IDs — DaiWrite + !all_same_id in
// FUSE_CMD_AXI_ADDR_ST
//
// The filter latches awuser for each phase of a DAI write:
//   latched_data_id0 ← awuser during WDATA_0 address phase
//   latched_data_id1 ← awuser during WDATA_1 address phase
//   latched_addr_id  ← awuser during ADDRESS address phase
//   latched_cmd_id   ← awuser during CMD address phase
//
// all_same_id requires all these to match (for secret addresses,
// data_id1==data_id0 is also checked).
//
// By writing WDATA_0 and WDATA_1 with MCU user, then switching to Caliptra
// core user for ADDRESS and CMD, we create:
//   latched_data_id0 = MCU,     latched_data_id1 = MCU
//   latched_addr_id  = Caliptra, latched_cmd_id   = Caliptra
//
// wr_req_allowed is true (Caliptra core cmd_id matches entry[0] for the
// secret range), so the DaiWrite + !wr_req_allowed branch is skipped. But
// all_same_id evaluates to:
//   ((MCU==MCU)|!true) && (MCU==Caliptra) && (Caliptra==Caliptra)
//   = true && false && true = false
//
// So the DaiWrite + !all_same_id condition fires: discard_fuse_write = 1.
//
// We do the register writes manually (not via dai_wr) because we need to
// switch awuser identity between the WDATA and ADDRESS phases.
//----------------------------------------------------------------------------
bool test_dai_write_mixed_ids(void) {
    VPRINTF(LOW, "\n--- Scenario 3: DaiWrite + !all_same_id in FUSE_CMD_AXI_ADDR_ST ---\n");

    if (!wait_dai_op_idle(0)) return false;

    const partition_t uds = partitions[SECRET_MANUF_PARTITION];

    // Phase 1: Write WDATA registers with MCU identity.
    // This latches latched_data_id0 and latched_data_id1 as MCU user.
    revoke_grant_mcu_for_fc_writes();
    mcu_sleep(20);

    VPRINTF(LOW, "DEBUG: Writing WDATA_0 with MCU user\n");
    lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_0, 0xA5A5A5A5);

    VPRINTF(LOW, "DEBUG: Writing WDATA_1 with MCU user\n");
    lsu_write_32(SOC_OTP_CTRL_DAI_WDATA_RF_DIRECT_ACCESS_WDATA_1, 0x5A5A5A5A);

    // Phase 2: Switch to Caliptra core identity for ADDRESS and CMD.
    // This latches latched_addr_id and latched_cmd_id as Caliptra core user.
    // The mismatch between data IDs (MCU) and addr/cmd IDs (Caliptra) makes
    // all_same_id evaluate to false.
    grant_caliptra_core_for_fc_writes();
    mcu_sleep(20);

    // Writing ADDRESS also sets caliptra_secret_access=true (addr 0x48 is in
    // the secret range [0x48,0xF0]), which activates the data_id1==data_id0
    // sub-check in all_same_id.
    VPRINTF(LOW, "DEBUG: Writing ADDRESS 0x%08X with Caliptra core user\n", uds.address);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, uds.address);

    // Writing CMD with DaiWrite (0x2). The filter checks all_same_id and
    // discards because data IDs don't match addr/cmd IDs.
    VPRINTF(LOW, "DEBUG: Writing CMD DaiWrite(0x2) with Caliptra core user\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, 0x2);

    // Expect DAI error due to filter discarding the write.
    if (!wait_dai_op_idle(OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
        VPRINTF(LOW, "ERROR: Unexpected status from mixed-ID DaiWrite\n");
        return false;
    }

    VPRINTF(LOW, "PASS: Scenario 3 completed - DaiWrite with mixed IDs correctly discarded\n");
    return true;
}

//----------------------------------------------------------------------------
// Scenario 4: DaiZeroize with mismatched addr/cmd IDs — DaiZeroize +
// !addr_and_cmd_same_id in FUSE_CMD_AXI_ADDR_ST
//
// addr_and_cmd_same_id = (latched_addr_id == latched_cmd_id).
// By writing ADDRESS with MCU user and CMD with Caliptra core user, we
// create latched_addr_id != latched_cmd_id.
//
// To reach the DaiZeroize + !addr_and_cmd_same_id branch, two earlier
// DaiZeroize checks in FUSE_CMD_AXI_ADDR_ST must be FALSE:
//   - DaiZeroize + (caliptra_secret_access && !FIPS_ZEROIZATION_CMD_i):
//     We target SW_MANUF_PARTITION (address 0xF8), which is OUTSIDE the
//     secret range [0x48,0xF0], so caliptra_secret_access=false. This
//     makes the entire condition false regardless of FIPS signal.
//   - DaiZeroize + !wr_req_allowed:
//     latched_cmd_id is Caliptra core, and entry[0] of access_control_table
//     covers [0x00,0x3FD8] for Caliptra core, so wr_req_allowed=true.
//
// With both earlier checks FALSE, the condition evaluates:
//   DaiZeroize && write_event && !addr_and_cmd_same_id
//   = true && true && true  ->  discard_fuse_write = 1.
//
// We do the register writes manually because we need to switch awuser
// identity between the ADDRESS and CMD phases.
//----------------------------------------------------------------------------
bool test_dai_zeroize_mixed_ids(void) {
    VPRINTF(LOW, "\n--- Scenario 4: DaiZeroize + !addr_and_cmd_same_id in FUSE_CMD_AXI_ADDR_ST ---\n");

    if (!wait_dai_op_idle(0)) return false;

    // SW_MANUF_PARTITION is at offset 0xF8, which is outside the secret range
    // [0x48,0xF0]. This ensures caliptra_secret_access=false, so the FIPS
    // zeroization check is not triggered.
    const partition_t sw_manuf = partitions[SW_MANUF_PARTITION];

    // Phase 1: Write ADDRESS with MCU identity.
    // This latches latched_addr_id = MCU user.
    revoke_grant_mcu_for_fc_writes();
    mcu_sleep(20);

    VPRINTF(LOW, "DEBUG: Writing ADDRESS 0x%08X with MCU user\n", sw_manuf.address);
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_ADDRESS, sw_manuf.address);

    // Phase 2: Switch to Caliptra core identity for CMD.
    // This latches latched_cmd_id = Caliptra core user.
    // Now latched_addr_id (MCU) != latched_cmd_id (Caliptra), making
    // addr_and_cmd_same_id = false.
    grant_caliptra_core_for_fc_writes();
    mcu_sleep(20);

    // Writing CMD with DaiZeroize (0x8). The filter checks addr_and_cmd_same_id
    // and discards because the ADDRESS writer differs from the CMD writer.
    VPRINTF(LOW, "DEBUG: Writing CMD DaiZeroize(0x8) with Caliptra core user\n");
    lsu_write_32(SOC_OTP_CTRL_DIRECT_ACCESS_CMD, 0x8);

    // Expect DAI error due to filter discarding the zeroize.
    if (!wait_dai_op_idle(OTP_CTRL_STATUS_DAI_ERROR_MASK)) {
        VPRINTF(LOW, "ERROR: Unexpected status from mixed-ID DaiZeroize\n");
        return false;
    }

    VPRINTF(LOW, "PASS: Scenario 4 completed - DaiZeroize with mixed IDs correctly discarded\n");
    return true;
}

void main(void) {
    VPRINTF(LOW, "=================\nMCU Caliptra Boot Go\n=================\n\n");

    // Standard Caliptra subsystem initialization.
    // mcu_cptra_init_d() brings up the MCU, loads fuses, and sets fuse_done.
    VPRINTF(LOW, "INFO: Initializing Caliptra subsystem...\n");
    mcu_cptra_init_d();

    bool passed = true;

    // Scenario 1: trigger_table_check in FUSE_ADDR_AXI_WR_ST
    if (!test_double_address_write()) passed = false;

    // Reset FC/LCC between scenarios to clear the filter FSM back to RESET_ST,
    // ensuring each scenario starts from a clean IDLE_ST after init completes.
    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0)) passed = false;

    // Scenario 2: DaiWrite + !wr_req_allowed in FUSE_CMD_AXI_ADDR_ST
    if (!test_unauthorized_dai_write()) passed = false;

    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0)) passed = false;

    // Scenario 3: DaiWrite + !all_same_id in FUSE_CMD_AXI_ADDR_ST
    if (!test_dai_write_mixed_ids()) passed = false;

    reset_fc_lcc_rtl();
    if (!wait_dai_op_idle(0)) passed = false;

    // Scenario 4: DaiZeroize + !addr_and_cmd_same_id in FUSE_CMD_AXI_ADDR_ST
    if (!test_dai_zeroize_mixed_ids()) passed = false;

    mcu_sleep(160);
    VPRINTF(LOW, "\nINFO: MCU Caliptra Boot sequence completed.\n");

    // Signal pass/fail to the testbench.
    SEND_STDOUT_CTRL(passed ? TB_CMD_TEST_PASS : TB_CMD_TEST_FAIL);
}
