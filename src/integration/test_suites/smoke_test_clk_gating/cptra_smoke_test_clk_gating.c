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
// Caliptra CORE-side firmware for smoke_test_clk_gating (SS-level).
//
// Purpose:
//   Exercise Caliptra CORE clock gating at the subsystem level. This closes a
//   coverage gap: caliptra-core clk_gate is only tested in caliptra-rtl's core
//   TB today; at the SS level MCI's clk_gate is tied off and no SS test enables
//   the core's CPTRA_CLK_GATING_EN.
//
//   The MCU firmware (mcu_smoke_test_clk_gating.c) enables clock gating by
//   writing CPTRA_CLK_GATING_EN (SoC-writable / Caliptra-RO). This core firmware:
//     1. Polls its RO copy of CPTRA_CLK_GATING_EN until the enable bit reads 1
//        (guarantees gating is armed before the halt -> unambiguous waveform).
//     2. Halts the VeeR core via the mpmc CSR (0x7c6 = 0x03) using the shared
//        clk_gate helpers, with internal timer0 as a DETERMINISTIC wake source
//        so the test always self-progresses (no TB-only services needed).
//     3. Confirms the core resumed after each halt/wake, then hands the pass
//        token to the MCU via the SS debug-service response register.
//
//   NOTE: We deliberately do NOT use core-TB-only stdout services such as
//   SEND_STDOUT_CTRL(0xf2)/(0xf8)/(0xe9) that exist in caliptra-rtl's core TB;
//   those do not exist in the SS TB. The enable comes from the real MCU AXI
//   write, and every wake here is a genuine internal-timer0 interrupt.
//

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "printf.h"
#include "clk_gate.h"
#include "soc_ifc.h"

volatile char*    stdout     = (char *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {

    volatile uint32_t * soc_ifc_clk_gating_en = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_CLK_GATING_EN;
    volatile uint32_t * soc_ifc_flow_status   = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS;

    // Internal timer0 wake configuration (matches caliptra-rtl clk_gate.c values):
    //   mitb0          = internal timer0 upper bound (short => quick self-wake)
    //   mie_timer0_en  = machine interrupt enable bit for internal timer0
    const uint32_t mitb0_short = 0x00000020;
    const uint32_t mitb0_long  = 0x00000500;
    const uint32_t mie_timer0_en = 0x20000000;

    // Deterministic mailbox response payload the core sends back to the MCU
    // when it wakes on the mailbox command (scenario 3).
    mbox_op_s op;
    const uint32_t mbox_resp_dlen = 64; // bytes (16 words)
    const uint32_t mbox_resp_data[16] = { 0xa5a5a5a5, 0x5a5a5a5a, 0xdeadbeef, 0xcafef00d,
                                          0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff,
                                          0x0f0f0f0f, 0xf0f0f0f0, 0x12345678, 0x9abcdef0,
                                          0x11223344, 0x55667788, 0x99aabbcc, 0xddeeff00 };

    VPRINTF(LOW, "-------------------------------------------------\n");
    VPRINTF(LOW, " CLP_CORE: SS CLK GATING smoke test\n");
    VPRINTF(LOW, "-------------------------------------------------\n");

    // Configure and enable vectored interrupts so the internal-timer0 interrupt
    // can wake the core out of the mpmc halt.
    init_interrupts();

    //--------------------------------------------------------------------
    // Step 1: Wait for the MCU to arm clock gating.
    //         CPTRA_CLK_GATING_EN is Caliptra-RO; the MCU (SoC master) sets it.
    //--------------------------------------------------------------------
    VPRINTF(LOW, "CLP_CORE: waiting for MCU to enable CPTRA_CLK_GATING_EN...\n");
    while ((*soc_ifc_clk_gating_en & SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK) == 0) {
        // spin until SoC-side enable is observed
    }
    VPRINTF(LOW, "CLP_CORE: clock gating is ENABLED and armed.\n");

    //--------------------------------------------------------------------
    // Step 2 (PRIMARY, deterministic): halt with internal timer0 as the wake
    //         source. This self-wakes with no TB assistance, so the test always
    //         makes forward progress.
    //--------------------------------------------------------------------
    VPRINTF(LOW, "CLP_CORE: [scenario 1] about to HALT core (wake=internal timer0)\n");
    set_mit0_and_halt_core(mitb0_short, mie_timer0_en);
    VPRINTF(LOW, "CLP_CORE: [scenario 1] core AWAKE after internal timer0 wake\n");

    //--------------------------------------------------------------------
    // Step 3 (SECONDARY): halt again with internal timer0 as the wake source.
    //         During this halt the MCU is actively polling over AXI (spinning
    //         in mcu_cptra_poll_mb_ready reading CPTRA_FLOW_STATUS), exercising
    //         the soc_ifc clock domain staying alive while the core clock is
    //         gated. Timer0 still self-wakes, keeping the scenario deterministic.
    //         NOTE: READY_FOR_MB_PROCESSING is intentionally NOT set here; it is
    //         only asserted in scenario 3 so the MCU's mailbox send is race-free
    //         and the mailbox wake is unambiguous.
    //--------------------------------------------------------------------
    VPRINTF(LOW, "CLP_CORE: [scenario 2] about to HALT core (SoC AXI active, wake=internal timer0)\n");
    set_mit0_and_halt_core(mitb0_long, mie_timer0_en);
    VPRINTF(LOW, "CLP_CORE: [scenario 2] core AWAKE after internal timer0 wake\n");

    //--------------------------------------------------------------------
    // Step 4 (scenario 3, PRIMARY mailbox-wake): halt the core with ONLY the
    //         RISC-V external interrupt enabled (mie = 0x800, timer0 DISABLED).
    //         The only event that can wake the core is the soc_ifc
    //         notif_cmd_avail notification (routed to mie bit 11 / external
    //         interrupt) which fires when the MCU writes the mailbox EXECUTE
    //         bit. If the mailbox-wake path were broken the core would stay
    //         halted forever and the MCU's blocking mailbox poll would hang -
    //         a detectable timeout. This is the strong mailbox-wake check.
    //--------------------------------------------------------------------
    // Signal the MCU (SoC master) that it may now send the mailbox command.
    VPRINTF(LOW, "CLP_CORE: [scenario 3] signalling READY_FOR_MB_PROCESSING to SoC\n");
    *soc_ifc_flow_status = SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK;

    // CRITICAL for mailbox-wake: VeeR-EL2 fw-halt (mpmc.halt) can only be woken
    // by an EXTERNAL interrupt when that interrupt is at the MAXIMUM PIC priority.
    // In el2_pic_ctrl, mhwakeup (the sole external wake source for a halted core)
    // asserts only when the highest pending/enabled priority == maxint (=15 in
    // standard order). init_interrupts() programs SOC_IFC_NOTIF at priority 7,
    // which can NEVER wake a halted core -> the mailbox command would hang.
    // Raise SOC_IFC_NOTIF to priority 15 so the incoming mailbox notif_cmd_avail
    // asserts mhwakeup and genuinely wakes the fw-halted core.
    volatile uint32_t * const meipls = (uint32_t *) VEER_MM_PIC_MEIPLS;
    meipls[VEER_INTR_VEC_SOC_IFC_NOTIF] = 0xF; // max priority -> asserts mhwakeup
    __asm__ volatile ("fence");

    VPRINTF(LOW, "CLP_CORE: [scenario 3] about to HALT - waiting for MCU mailbox command (mbox-wake)\n");
    // Low-level halt using ONLY the external interrupt (mie bit 11 = 0x800).
    // Deliberately DO NOT enable internal timer0 so the only possible wake
    // source is the mailbox notif_cmd_avail -> external interrupt.
    //   mie     (CSR 0x304) = 0x00000800  (external interrupt only, no timer0)
    //   mstatus (CSR 0x300) = 0x08        (global machine interrupt enable)
    //   mpmc    (CSR 0x7c6) = 0x03        (halt / clock-gate the core)
    __asm__ volatile ("csrw    %0, %1" : : "i" (0x304), "r" (0x00000800));
    __asm__ volatile ("csrwi   %0, %1" : : "i" (0x300), "i" (0x08));
    __asm__ volatile ("csrwi   %0, %1" : : "i" (0x7c6), "i" (0x03));

    //--------------------------------------------------------------------
    // On wake: confirm the mailbox command actually arrived, then service it
    // exactly like the caliptra-rtl smoke_test_mbox_cg reference:
    //   - read the command + dlen
    //   - drain the input payload
    //   - write a response payload
    //   - set DATA_READY so the SoC/MCU can read the response
    //--------------------------------------------------------------------
    // Confirm EXECUTE is set (the MCU's EXECUTE write is what woke us).
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0);

    op = soc_ifc_read_mbox_cmd();
    VPRINTF(LOW, "CLP_CORE: [scenario 3] mbox cmd=0x%x dlen=%d - draining input\n", op.cmd, op.dlen);

    // Drain the input payload from the mailbox.
    while (op.dlen) {
        (void) soc_ifc_mbox_read_dataout_single();
        if (op.dlen < 4) {
            op.dlen = 0;
        } else {
            op.dlen -= 4;
        }
    }

    // Write a deterministic response payload back to the MCU.
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN, mbox_resp_dlen);
    for (uint32_t ii = 0; ii < mbox_resp_dlen / 4; ii++) {
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_resp_data[ii]);
    }

    // Set response-ready status so the MCU's mailbox poll completes.
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, DATA_READY);
    VPRINTF(LOW, "CLP_CORE: core AWAKE via MAILBOX command - serviced\n");

    // Wait for the SoC/MCU to clear EXECUTE (end of the mailbox handshake).
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK));

    //--------------------------------------------------------------------
    // Step 5: hand the pass token to the MCU and end the core test.
    //--------------------------------------------------------------------
    VPRINTF(LOW, "CLP_CORE: clk-gating halt/wake complete. Signalling MCU. PASS.\n");
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP,
                 SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK);

    SEND_STDOUT_CTRL(0xff); // Core-side success / end of test
}
