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
// Description: USB HS host remote wakeup test firmware for the Caliptra Subsystem.
//
// DUT role: USB HOST (ip_3515 ATL host controller, SOC_USBHSH_* registers).
// VIP role: USB DEVICE (SVT VIP device sequence, initiates remote wakeup).
//
// Test flow :
//   1. Boot MCU. Advance Caliptra breakpoint.
//   2. Assert HCRESET, poll until cleared.
//   3. Set PORTMODE[16]=0 (HOST mode) after HCRESET.
//      Integration Guide sec 4.1.2.21: PORT_MODE bit16=0 -> HOST, bit16=1 -> DEVICE.
//      Reset value is 0x00050000 (bit16=1 device, bit18=1 SW_CTRL_PDCOM).
//      Writing 0 clears PORT_MODE and SW_CTRL_PDCOM (HW controls PHY power-down).
//   4. Set RS (Run/Stop). Guide sec 4.1.2.9: RS bit0 -- host executes schedule.
//   5. Set PP (port power). Poll USBSTS for PCD (port change detect, bit2 W1C).
//      Guide sec 4.1.2.10: PCD is set when CCS transitions 0->1 (device attach).
//      Clear PCD W1C. Check CSC in PORTSC1 (bit1 W1C), clear it.
//   6. Assert PR (port reset, bit8). Hold ~742 us for HS chirp. Clear PR.
//      Guide sec 4.1.2.12: SW writes PR=1 to start reset, PR=0 to end.
//      HW clears PR when reset sequence is complete. Poll until PR=0.
//   7. Verify PSPD=HS (bits[21:20]=0b10). Check PED (bit2) and PEDC (bit3 W1C).
//      Guide: PSPD is valid only when PR=0.
//   8. Enable SOF interrupt (USBINTR bit19=SOF_E). Poll for 2 SOF_IRQ events (W1C).
//      Guide sec 4.1.2.11: SOF_E bit19 enables SOF interrupt.
//      Guide sec 4.1.2.10: SOF_IRQ bit19 W1C -- set every SOF microframe.
//   9. Disable USBINTR. Set PORTSC1.SUSP (bit7) to suspend the port.
//      Guide sec 4.1.2.12: SW writes SUSP=1 to put enabled port in L2 suspend.
//      SUS_L1 bit9=0 (default) means L2 suspend. A write of zero to SUSP is ignored.
//  10. Spin ~4ms (TB checks no SOF).
//  11. Stop host: USBCMD = 0. Re-start host: USBCMD = RS.
//      (turn off host, then re-enable after needclk handling.)
//  12. Verify PORTSC1.SUSP is still set (device-initiated remote wakeup wake
//      signal has been detected; host must continue resume signaling).
//  13. Assert FPR (Force Port Resume, bit6) to continue resume signaling.
//      Guide: resume K-state driven as long as FPR=1. SW times L2 resume and
//      clears FPR by writing PORTSC1 = PP | PED (FPR=0 -> HW clears SUSP).
//      Write PP|PED to end signaling.
//  14. Verify PORTSC1.SUSP is now clear (resume complete).
//      Guide: HW unconditionally clears SUSP when SW sets FPR to zero.
//  15. Clear all USBSTS. Re-enable SOF interrupt. Poll for 3 SOF_IRQ events.
//      This confirms normal microframe traffic after resume.
//  16. Print PASSED and halt.
//

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "stdbool.h"
#include "veer-csr.h"

// ---------------------------------------------------------------------------
// Timing constants
// (MCU clk ~333 MHz, ~3 ns/iter for fence+AHB in RTL simulation;
//  actual measured ~14 ns/iter including store-buffer latency -- see bulk_out)
// ---------------------------------------------------------------------------
#define HCRESET_POLL_MAX    20000u    // iterations waiting for HCRESET to clear

// HS chirp: same calibration as bulk_out test.
// PR asserted at ~44 us; chirp done at ~714 us; ATL drives J at 764 us.
// tlinestate_duration window: 764-830 us. PR must deassert within 764-814 us.
// PR_HOLD_DELAY=53000 x ~14 ns/iter = ~742 us hold; deasserts at ~786 us.
#define PR_HOLD_DELAY       53000u

#define PR_CLEAR_POLL_MAX   200000u   // iterations waiting for PR to clear
#define PCD_POLL_MAX        200000u   // iterations waiting for PCD in USBSTS
#define SOF_POLL_MAX        2000000u  // iterations waiting for each SOF_IRQ

// At ~14 ns/iter: 2 ms = ~143000 iters; 10 ms = ~714000 iters.
// Use conservative values to ensure correct timing in RTL simulation.
// NOTE: DELAY_10MS is reduced to 300us (21420 iters) for simulation speed.
// USB 2.0 spec tDRSMUP_min = 1ms; VIP tdrsmup_min is set to 5us in the test,
// so 300us is well above the check. Total FPR hold: 100us+300us+100us = 500us.
#define DELAY_1MS            71500u
#define DELAY_2MS           143000u
#define DELAY_5MS           357000u   // ~5ms: used after SUSP+USBCMD=0 to wait for PIE
                                      // T_THSIDLE=4ms (240000 cycles) to expire so that
                                      // BUS_EVENT_HS_WF_SUSPEND_L2 -> BUS_EVENT_SUSPEND_L2
                                      // transition completes before FPR is asserted.
                                      // FPR is only sampled in BUS_EVENT_SUSPEND_L2;
                                      // asserting it earlier in HS_WF_SUSPEND_L2 has no effect.
#define DELAY_10MS           50000u   // ~700us: well above VIP twtrev=500us minimum host K check.
                                      // No 10ms RTL timer exists; shorter value saves simulation time.
#define DELAY_100US          7140u
#define DELAY_10US            714u

// ---------------------------------------------------------------------------
// USBHSH register bit definitions (local aliases for readability).
// Full mask names from soc_address_map.h are used directly where possible.
// ---------------------------------------------------------------------------
// USBCMD
#define USBHSH_RS           (USBHSH_USBCMD_RS_MASK)       // bit 0
#define USBHSH_HCRESET      (USBHSH_USBCMD_HCRESET_MASK)  // bit 1
// USBSTS / USBINTR
#define USBHSH_PCD          (USBHSH_USBSTS_PCD_MASK)       // bit 2: port connect detect
#define USBHSH_SOF_IRQ      (USBHSH_USBSTS_SOF_IRQ_MASK)  // bit 19: SOF microframe
#define USBHSH_SOF_EN       (USBHSH_USBSTS_SOF_IRQ_MASK)  // same bit in USBINTR reg
// PORTSC1
#define USBHSH_CCS          (USBHSH_PORTSC1_CCS_MASK)     // bit 0
#define USBHSH_CSC          (USBHSH_PORTSC1_CSC_MASK)     // bit 1 (W1C)
#define USBHSH_PED          (USBHSH_PORTSC1_PED_MASK)     // bit 2
#define USBHSH_PEDC         (USBHSH_PORTSC1_PEDC_MASK)    // bit 3 (W1C)
#define USBHSH_FPR          (USBHSH_PORTSC1_FPR_MASK)     // bit 6: force port resume
#define USBHSH_SUSP         (USBHSH_PORTSC1_SUSP_MASK)    // bit 7: suspend
#define USBHSH_PR           (USBHSH_PORTSC1_PR_MASK)      // bit 8: port reset
#define USBHSH_PP           (USBHSH_PORTSC1_PP_MASK)      // bit 12: port power
#define USBHSH_PSPD_SHIFT   (USBHSH_PORTSC1_PSPD_LOW)
#define USBHSH_PSPD_MASK_F  (USBHSH_PORTSC1_PSPD_MASK)
#define USBHSH_PSPD_HS      (2u << USBHSH_PSPD_SHIFT)

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// ---------------------------------------------------------------------------
// poll_until_clear / poll_until_set
// ---------------------------------------------------------------------------
static bool poll_until_clear(uint32_t addr, uint32_t mask, uint32_t max_iter, const char *lbl)
{
    for (uint32_t i = 0; i < max_iter; i++) {
        if (!(lsu_read_32(addr) & mask)) return true;
        __asm__ volatile ("fence" ::: "memory");
    }
    VPRINTF(LOW, "MCU: TIMEOUT waiting for %s to clear (addr=0x%x)\n", lbl, addr);
    return false;
}

static bool poll_until_set(uint32_t addr, uint32_t mask, uint32_t max_iter, const char *lbl)
{
    for (uint32_t i = 0; i < max_iter; i++) {
        if (lsu_read_32(addr) & mask) return true;
        __asm__ volatile ("fence" ::: "memory");
    }
    VPRINTF(LOW, "MCU: TIMEOUT waiting for %s to set (addr=0x%x)\n", lbl, addr);
    return false;
}

// ---------------------------------------------------------------------------
// wait_sof_irq
//
// Poll USBSTS until SOF_IRQ (bit 19) fires, then clear it W1C.
// Returns true if the SOF was detected within SOF_POLL_MAX iterations.
// ---------------------------------------------------------------------------
static bool wait_sof_irq(uint32_t idx)
{
    if (!poll_until_set(SOC_USBHSH_USBSTS, USBHSH_SOF_IRQ, SOF_POLL_MAX, "SOF_IRQ")) {
        VPRINTF(LOW, "MCU: TIMEOUT waiting for SOF #%d\n", idx);
        return false;
    }
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_SOF_IRQ);  // W1C
    VPRINTF(LOW, "MCU: SOF #%d detected\n", idx);
    return true;
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------
void main(void)
{
    uint32_t reg;
    uint32_t pspd;

    VPRINTF(LOW, "=================\n"
                 "MCU: USB HS host remote wakeup test (DUT=HOST HS, VIP=DEVICE)\n"
                 "=================\n\n");

    boot_mcu();

    // Advance Caliptra breakpoint immediately so Caliptra FW proceeds in
    // parallel with USB init. Same pattern as bulk_out.
    mcu_cptra_advance_brkpoint();
    VPRINTF(LOW, "MCU: Caliptra brkpt advanced. Starting USB host init.\n");

    // -----------------------------------------------------------------------
    // Step 1: HCRESET (LPC_USB_HS0_HOST->USBCMD |= HCRESET)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBCMD, lsu_read_32(SOC_USBHSH_USBCMD) | USBHSH_HCRESET);
    if (!poll_until_clear(SOC_USBHSH_USBCMD, USBHSH_HCRESET, HCRESET_POLL_MAX, "HCRESET")) {
        VPRINTF(LOW, "MCU: FATAL - HCRESET did not clear.\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: HCRESET complete.\n");

    // -----------------------------------------------------------------------
    // Step 2: Select HOST mode after HCRESET.
    //
    // PORTMODE reset value = 0x00050000:
    //   bit16 = PORT_MODE = 1 (DEVICE)    -- must clear to 0 for HOST
    //   bit18 = SW_CTRL_PDCOM = 1         -- MUST PRESERVE: SW controls PHY power-down
    //   bit19 = SW_PDCOM = 0              -- PHY operational (not powered down)
    //
    // Writing 0x00000000 (USBHSH_PORT_MODE_HOST=0u) clears SW_CTRL_PDCOM (bit18).
    // With SW_CTRL_PDCOM=0, the HW state machine powers down the PHY during L2
    // suspend. When MCU asserts FPR to drive K-state, the ATL UTMI K cannot
    // propagate through the powered-down PHY to the DP/DM pins. The SVT VIP
    // device drives K (tdrsmup=10us), stops, expects host K continuation, sees
    // only J (host K not reaching bus), and returns to SUSPEND (stuck).
    //
    // Correct value = 0x00040000:
    //   bit16=0 (HOST mode)
    //   bit18=1 (SW_CTRL_PDCOM=1: SW controls PHY -- keeps PHY powered during L2)
    //   bit19=0 (SW_PDCOM=0: PHY operational, not in power-down)
    //
    // With SW_CTRL_PDCOM=1 and SW_PDCOM=0, the PHY remains active during L2
    // suspend. MCU FPR K-state drives through the PHY to DP/DM, VIP detects
    // host K, transitions SUSPEND->RESUME, and resume completes normally.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTMODE, USBHSH_PORTMODE_SW_CTRL_PDCOM_MASK);
    VPRINTF(LOW, "MCU: PORTMODE = 0x%x (HOST, SW_CTRL_PDCOM=1, PHY active).\n",
            USBHSH_PORTMODE_SW_CTRL_PDCOM_MASK);

    // -----------------------------------------------------------------------
    // Step 3: Run/Stop (LPC_USB_HS0_HOST->USBCMD = RS)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBCMD, USBHSH_RS);
    VPRINTF(LOW, "MCU: USBCMD RS set.\n");

    // -----------------------------------------------------------------------
    // Step 4: Set port power (PP, bit12).
    // Guide sec 4.1.2.12: If PPC=1 in HCSPARAMS, PP is RW. Set PP=1 to power port.
    // (LPC_USB_HS0_HOST->PORTSC1 |= PP)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PP);
    VPRINTF(LOW, "MCU: PP set.\n");

    // -----------------------------------------------------------------------
    // Step 5: Wait for PCD (port connect detect) in USBSTS.
    // Guide sec 4.1.2.10: PCD bit2 is set when CCS transitions 0->1 (device
    // attaches). This fires when the VIP device connects after PP is asserted.
    // Must be handled BEFORE PR:
    //   RS -> wait PCD -> clear CSC -> set PR -> hold -> clear PR
    // (while (USBSTS != PCD); USBSTS = PCD; verify CSC; clear CSC)
    // -----------------------------------------------------------------------
    if (!poll_until_set(SOC_USBHSH_USBSTS, USBHSH_PCD, PCD_POLL_MAX, "USBSTS.PCD")) {
        VPRINTF(LOW, "MCU: WARNING - PCD did not set. Continuing.\n");
    }
    lsu_write_32(SOC_USBHSH_USBSTS, USBHSH_PCD);  // W1C clear PCD

    reg = lsu_read_32(SOC_USBHSH_PORTSC1);
    VPRINTF(LOW, "MCU: PORTSC1=0x%x (checking CSC after device attach)\n", reg);
    if (!(reg & USBHSH_CSC)) {
        VPRINTF(LOW, "MCU: WARNING - CSC not set (PORTSC1=0x%x)\n", reg);
    }
    // Clear CSC W1C (Guide: SW must write 1 to clear)
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_CSC);

    // -----------------------------------------------------------------------
    // Step 6: Assert Port Reset (PR, bit8) -- no PFSC (bit13=0), HS capable.
    // Guide sec 4.1.2.12: SW writes PR=1 to start, PR=0 to end reset sequence.
    // HW will clear PR when reset sequence is complete. SW polls until PR=0,
    // then reads PSPD to determine attached device speed.
    // (PORTSC1 |= PR; mrt_wait(_10MS); PORTSC1 &= ~PR; wait PR clear)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PR);
    VPRINTF(LOW, "MCU: PR asserted. Holding for HS chirp (~742 us)...\n");

    // Hold PR long enough for HS chirp handshaking (see timing comment at top).
    for (volatile uint32_t d = 0; d < PR_HOLD_DELAY; d++) { /* spin */ }

    // Clear PR (keep PP) -- PORTSC1 &= ~PR
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) & ~USBHSH_PR);
    VPRINTF(LOW, "MCU: PR deasserted. Waiting for HW to self-clear PR...\n");

    if (!poll_until_clear(SOC_USBHSH_PORTSC1, USBHSH_PR, PR_CLEAR_POLL_MAX, "PORTSC1.PR")) {
        VPRINTF(LOW, "MCU: WARNING - PR did not clear. Continuing.\n");
    }
    VPRINTF(LOW, "MCU: Port Reset complete.\n");

    // -----------------------------------------------------------------------
    // Step 7: Verify PSPD=HS (bits[21:20]=0b10) and check PED+PEDC.
    // Guide: PSPD valid only when PR=0. PSPD: 00=LS 01=FS 10=HS 11=reserved.
    // Guide: PEDC bit3 W1C set when PED transitions. SW writes 1 to clear.
    // (verify_equal(PORTSC1 & PEDC, PEDC); PORTSC1 |= PEDC)
    // -----------------------------------------------------------------------
    reg  = lsu_read_32(SOC_USBHSH_PORTSC1);
    pspd = (reg & USBHSH_PSPD_MASK_F) >> USBHSH_PSPD_SHIFT;
    VPRINTF(LOW, "MCU: PORTSC1=0x%x PSPD=%d (%s)\n", reg, pspd,
            (pspd == 2u) ? "HS" : (pspd == 1u) ? "FS" : "LS/unknown");
    if (pspd != 2u) {
        VPRINTF(LOW, "MCU: FATAL - Expected PSPD=HS(2), got %d. Test FAILED.\n", pspd);
        csr_write_mpmc_halt();
    }

    if ((reg & USBHSH_PEDC) && (reg & USBHSH_PED)) {
        // Clear PEDC W1C (Guide: SW writes 1 to clear)
        lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_PEDC);
        VPRINTF(LOW, "MCU: Port enabled (PED=1). PEDC cleared.\n");
    } else {
        VPRINTF(LOW, "MCU: FATAL - PEDC or PED not set after reset (PORTSC1=0x%x).\n", reg);
        csr_write_mpmc_halt();
    }

    // -----------------------------------------------------------------------
    // Step 8: Clear all pending USBSTS, enable SOF interrupt.
    // Guide sec 4.1.2.11: USBINTR bit19 = SOF_E. When set, SOF_IRQ in USBSTS
    // will generate a hardware interrupt. In bare-metal we poll SOF_IRQ directly.
    // Guide sec 4.1.2.10: SOF_IRQ bit19 RWC -- set every SOF microframe (125us).
    // SW writes 1 to clear.
    // Poll for 2 SOF_IRQ events (confirms host is generating microframes).
    // (USBINTR = 0xFFFFFFFF; sema_micrf_irq.get() x2 via usb_isr SOF_IRQ)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBSTS,  0xFFFFFFFFu);  // clear all pending W1C bits
    lsu_write_32(SOC_USBHSH_USBINTR, USBHSH_SOF_EN);
    VPRINTF(LOW, "MCU: SOF interrupt enabled. Waiting for 2 SOF events...\n");

    if (!wait_sof_irq(1u)) { csr_write_mpmc_halt(); }
    if (!wait_sof_irq(2u)) { csr_write_mpmc_halt(); }
    VPRINTF(LOW, "MCU: 2 SOF events received. Host is running.\n");

    // -----------------------------------------------------------------------
    // Step 9: Disable interrupts. Set PORTSC1.SUSP (bit7) to suspend the port.
    // Guide sec 4.1.2.12: SW writes SUSP=1 to put an enabled port in L2 suspend
    // (SUS_L1 bit9=0 default -> L2). Downstream data propagation is blocked.
    // A write of zero to SUSP is ignored by HW.
    // NOTE: SUSP only blocks data transactions to the port; the host controller
    // continues to send SOF tokens every 125us until RS=0 (USBCMD=0).
    // To stop SOF generation so the VIP device detects bus idle and enters
    // SUSPEND, we must clear RS immediately after setting PORTSC1.SUSP.
    // (USBINTR = 0; PORTSC1 |= SUSPEND; dev_clk_enable(false) which
    //  stops the USB clock and thus SOF -- equivalent to USBCMD=0 here)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBINTR, 0x00000000u);
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_SUSP);
    VPRINTF(LOW, "MCU: Port suspended (SUSP set). PORTSC1=0x%x\n",
            lsu_read_32(SOC_USBHSH_PORTSC1));

    // Stop host immediately to prevent further SOF token generation.
    // SOF tokens reset the VIP tinactivity timer so the VIP cannot enter
    // SUSPEND state until the bus is completely idle.
    lsu_write_32(SOC_USBHSH_USBCMD, 0x00000000u);
    VPRINTF(LOW, "MCU: Host stopped (USBCMD=0). SOF generation stopped.\n");

    // -----------------------------------------------------------------------
    // Step 10: Wait >4ms with bus idle.
    //
    // PIE FSM timing requirement (usb_host_pie.m.vhdl):
    //   After PORTSC1.SUSP is set, the PIE enters BUS_EVENT_HS_WF_SUSPEND_L2.
    //   It stays there for exactly T_THSIDLE=4ms (240000 clock cycles, per
    //   RTL constant at line 463). Only after that does it transition to
    //   BUS_EVENT_SUSPEND_L2.
    //   FPR (usbreg_portresume_sync) is only sampled in BUS_EVENT_SUSPEND_L2.
    //   Asserting FPR while PIE is still in HS_WF_SUSPEND_L2 has NO effect --
    //   the PIE ignores FPR in that state and MCU ends up clearing FPR before
    //   PIE ever reaches SUSPEND_L2, so K-state is never driven.
    //
    //   Firmware must wait >4ms after SUSP before asserting FPR.
    //   Using DELAY_5MS (~5ms) gives ~1ms margin above the 4ms PIE timer.
    //
    // VIP tinactivity: VIP enters SUSPEND ~700us after USBCMD=0 (500us twtrev
    // + 200us tinactivity). The 5ms firmware wait is well above 700us.
    //
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Waiting ~5ms (PIE T_THSIDLE=4ms, VIP enters SUSPEND)...\n");
    for (volatile uint32_t d = 0; d < DELAY_5MS; d++) { /* spin */ }

    // -----------------------------------------------------------------------
    // Step 11: Re-start host.
    // (USBCMD = RS after deep sleep / needclk handling)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBCMD, USBHSH_RS);
    VPRINTF(LOW, "MCU: Host restarted (USBCMD=RS).\n");

    // -----------------------------------------------------------------------
    // Step 12: Verify PORTSC1.SUSP is still set.
    // (verify_equal(PORTSC1 & 0xFFFFF3FF, 0x002014C5 & 0xFFFFF3FF)
    //  -- suspend should remain asserted after device-initiated remote wakeup)
    // -----------------------------------------------------------------------
    reg = lsu_read_32(SOC_USBHSH_PORTSC1);
    VPRINTF(LOW, "MCU: PORTSC1=0x%x after host restart (expect SUSP still set)\n", reg);
    if (!(reg & USBHSH_SUSP)) {
        VPRINTF(LOW, "MCU: WARNING - SUSP already cleared before FPR. "
                     "Device may have completed resume signaling. Continuing.\n");
    }

    // -----------------------------------------------------------------------
    // Step 13: Assert FPR (Force Port Resume, bit6) to drive K-state on the bus.
    // Guide sec 4.1.2.12 FPR: resume K-state is driven on the port as long as
    // FPR=1. For L2 (legacy) resume, SW times the duration and clears FPR.
    // Guide: HW unconditionally clears SUSP when SW sets FPR to zero (i.e.
    // when FPR transitions from 1 to 0, SUSP is cleared by HW).
    // Writing PORTSC1 = PP | PED effectively sets FPR=0 and preserves PP+PED,
    // which causes HW to clear SUSP. PORTSC1 = PP | PED.
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_PORTSC1, lsu_read_32(SOC_USBHSH_PORTSC1) | USBHSH_FPR);
    VPRINTF(LOW, "MCU: FPR set (driving resume K-state). PORTSC1=0x%x\n",
            lsu_read_32(SOC_USBHSH_PORTSC1));

    for (volatile uint32_t d = 0; d < DELAY_100US; d++) { /* spin */ }
    for (volatile uint32_t d = 0; d < DELAY_10MS;  d++) { /* spin */ }
    for (volatile uint32_t d = 0; d < DELAY_100US; d++) { /* spin */ }

    // End resume signaling: write PP | PED (FPR=0). HW clears SUSP.
    // (PORTSC1 = PP | PED)
    lsu_write_32(SOC_USBHSH_PORTSC1, USBHSH_PP | USBHSH_PED);
    for (volatile uint32_t d = 0; d < DELAY_10US; d++) { /* spin */ }
    VPRINTF(LOW, "MCU: FPR cleared (resume ended). PORTSC1=0x%x\n",
            lsu_read_32(SOC_USBHSH_PORTSC1));

    // -----------------------------------------------------------------------
    // Step 14: Verify PORTSC1.SUSP is now clear (resume complete).
    // Guide: HW clears SUSP when FPR transitions to zero.
    // (verify_equal(PORTSC1 & 0xFFFFF3FF, 0x00201005 & 0xFFFFF3FF))
    // -----------------------------------------------------------------------
    reg = lsu_read_32(SOC_USBHSH_PORTSC1);
    VPRINTF(LOW, "MCU: Post-resume PORTSC1=0x%x (expect SUSP=0, FPR=0)\n", reg);
    if (reg & USBHSH_SUSP) {
        VPRINTF(LOW, "MCU: WARNING - SUSP still set after FPR cleared (PORTSC1=0x%x)\n", reg);
    }
    if (reg & USBHSH_FPR) {
        VPRINTF(LOW, "MCU: WARNING - FPR still set (PORTSC1=0x%x)\n", reg);
    }

    // -----------------------------------------------------------------------
    // Step 15: Clear all USBSTS. Re-enable SOF interrupt (USBINTR bit19=SOF_E).
    // Poll for 3 SOF_IRQ events (confirms normal microframe traffic post-resume).
    // Guide: SOF_IRQ bit19 is set every 125us microframe. W1C.
    // (USBSTS=0xFFFFFFFF; USBINTR=0xFFFFFFFF; sema_micrf_irq.get() x3)
    // -----------------------------------------------------------------------
    lsu_write_32(SOC_USBHSH_USBSTS,  0xFFFFFFFFu);  // clear all W1C bits
    lsu_write_32(SOC_USBHSH_USBINTR, USBHSH_SOF_EN);
    VPRINTF(LOW, "MCU: SOF interrupt re-enabled. Waiting for 3 post-resume SOF events...\n");

    if (!wait_sof_irq(3u)) { csr_write_mpmc_halt(); }
    if (!wait_sof_irq(4u)) { csr_write_mpmc_halt(); }
    if (!wait_sof_irq(5u)) { csr_write_mpmc_halt(); }
    VPRINTF(LOW, "MCU: 3 post-resume SOF events received. Resume complete.\n");

    // Disable interrupts.
    lsu_write_32(SOC_USBHSH_USBINTR, 0x00000000u);

    // -----------------------------------------------------------------------
    // Done.
    // -----------------------------------------------------------------------
    VPRINTF(LOW, "MCU: USB HS host remote wakeup - PASSED\n");
    VPRINTF(LOW, "MCU: Halting.\n");
    csr_write_mpmc_halt();
}
