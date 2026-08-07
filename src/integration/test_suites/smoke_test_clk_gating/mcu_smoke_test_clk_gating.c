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

//
// MCU-side firmware for smoke_test_clk_gating (SS-level Caliptra CORE clock gating).
//
// Purpose:
//   The MCU is the SoC-side AXI master. It boots the Caliptra core and then
//   enables Caliptra CORE clock gating by writing the SoC-writable /
//   Caliptra-RO register SOC_SOC_IFC_REG_CPTRA_CLK_GATING_EN. The core firmware
//   (cptra_smoke_test_clk_gating.c) confirms the enable is armed, then performs
//   the VeeR mpmc halt and self-wakes via internal timer0.
//
//   The MCU write is intentionally issued EARLY (before the core reaches its
//   halt point) so that clock gating is unambiguously armed when the core halts,
//   producing a clean waveform. The MCU then busy-polls the SS debug-service
//   response register over AXI until the core signals completion. This polling
//   is also the "SoC-side AXI activity" the user asked for: it keeps the
//   soc_ifc clock domain alive while the Caliptra RISC-V core clock is gated.
//

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lc_ctrl_address_map.h"
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
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

void main (void) {
    uint32_t core_done;

    VPRINTF(LOW, "=================================================\n");
    VPRINTF(LOW, " MCU: SS CLK GATING smoke test (SoC-side master)\n");
    VPRINTF(LOW, "=================================================\n");

    // Standard SS init: program fuses, run BootFSM handshake and bring the
    // Caliptra core out of reset so its firmware starts executing. Also make
    // the MCU a valid Caliptra-mailbox AXI user (writes CPTRA_MBOX_VALID_AXI_USER_0
    // = MCU LSU AXI user and locks it) so the core mailbox accepts MCU writes -
    // required for the scenario-3 mailbox-command wake.
    mcu_cptra_init_d(.cfg_skip_set_fuse_done=false,
                     .cfg_enable_cptra_mbox_user_init=true);

    // Enable Caliptra CORE clock gating EARLY, before the core reaches its
    // halt point. This register is SoC-writable / Caliptra-RO, so it must be
    // driven from the MCU AXI master. The core firmware polls its RO copy
    // (CLP_SOC_IFC_REG_CPTRA_CLK_GATING_EN) until this bit reads 1 before it
    // halts, guaranteeing gating is armed.
    VPRINTF(LOW, "MCU: enabling Caliptra CORE clock gating (CPTRA_CLK_GATING_EN=1)\n");
    lsu_write_32(SOC_SOC_IFC_REG_CPTRA_CLK_GATING_EN,
                 SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK);

    // Read back over AXI to confirm the write landed (Caliptra-RO from core side,
    // but SoC-side read reflects the stored value).
    if ((lsu_read_32(SOC_SOC_IFC_REG_CPTRA_CLK_GATING_EN) &
         SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK) == 0) {
        VPRINTF(FATAL, "MCU: ERROR - CPTRA_CLK_GATING_EN did not set!\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    VPRINTF(LOW, "MCU: clock gating armed. Core may now halt.\n");

    // Scenarios 1 & 2 (core-side timer0 self-wake halts): block here polling
    // CPTRA_FLOW_STATUS.READY_FOR_MB_PROCESSING over AXI. The core only sets
    // READY right before its scenario-3 (external-interrupt-only) halt, so this
    // poll spins - issuing repeated AXI reads - throughout the core's scenario
    // 1/2 clock-gated halts (keeping the soc_ifc clock domain alive during core
    // halt) and unblocks exactly when the core is ready for the mailbox command.
    VPRINTF(LOW, "MCU: polling READY_FOR_MB_PROCESSING (AXI active during core halts)\n");
    mcu_cptra_poll_mb_ready();

    // Scenario 3: send a Caliptra-core mailbox command. mcu_cptra_mbox_cmd()
    // acquires MBOX_LOCK, writes CMD (response required), DLEN and DATAIN, then
    // sets the EXECUTE bit. That EXECUTE write asserts the soc_ifc
    // notif_cmd_avail notification -> RISC-V external interrupt (mie bit 11),
    // which is the ONLY enabled wake source for the core's scenario-3 halt, so
    // it wakes the clock-gated, halted core. The function then blocks until the
    // core responds (MBOX_STATUS == DATA_READY), reads the response and clears
    // EXECUTE. Completion of this blocking call proves the core woke on the
    // mailbox command and serviced it.
    VPRINTF(LOW, "MCU: sending Caliptra-core mailbox command (EXECUTE = mbox wake trigger)\n");
    mcu_cptra_mbox_cmd();
    VPRINTF(LOW, "MCU: mailbox response received - core woke on mailbox command\n");

    // Busy-poll the SS debug-service response register over AXI until the core
    // firmware reports completion. The core writes this done token only after
    // it has serviced the mailbox, so the mailbox exchange always precedes this
    // final wait.
    VPRINTF(LOW, "MCU: polling for core completion (final done token)\n");
    core_done = 0;
    while (core_done != SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK) {
        core_done = lsu_read_32(SOC_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP) &
                    SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK;
    }

    VPRINTF(LOW, "MCU: core signalled clk-gating halt/wake complete. PASS.\n");

    // Small settle loop so the core's final prints flush before the sim ends.
    for (uint32_t ii = 0; ii < 50; ii++) {
        __asm__ volatile ("nop");
    }

    SEND_STDOUT_CTRL(0xff); // MCU-side success / end of test
}
