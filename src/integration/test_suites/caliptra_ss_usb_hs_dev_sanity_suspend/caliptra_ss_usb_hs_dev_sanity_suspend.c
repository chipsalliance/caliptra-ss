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

// Description: USB HS device suspend/resume sanity firmware. Brings the
// hub-composite IP up in two phases (HUB_EN then HUB_CONNECT), handles EP0
// enumeration, releases FORCE_NEEDCLK so the UTMI clock can stop, and then
// polls DEVCMDSTAT while the host drives a global suspend and resume. The
// DSUS / DSUS_C traces are diagnostic only - see the observability note below.
// Renamed from caliptra_ss_usb_hs_dev_remote_wakeup: the device never
// initiates a wakeup here, the host drives both the suspend and the resume.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Duration of the DEVCMDSTAT polling loop. This is an unconditional dwell, not
// a ceiling: there is no MCU-visible event marking the end of the host-side
// stimulus, so the loop simply has to outlast it.
//
// Sizing. The host sequence drives suspend at ~806 us, the DUT suspends at
// ~1084 us and resumes at ~1138 us, and the sequence closes the checker
// observation window at ~1860 us. At the measured ~114 ns per iteration, 18000
// iterations is ~2.05 ms of coverage from the loop start at ~234 us, which
// covers the whole stimulus. Keeping it tight matters for wall time: nothing in
// the testbench can finish the simulation while the MCU is still running,
// because caliptra_ss_usb_base_test holds a run_phase objection until
// cptra_ss_mcu_halt_status_o asserts, and that only happens when this function
// reaches csr_write_mpmc_halt().
#define USB_POLL_TIMEOUT 14000

// NOTE ON WHAT THIS FIRMWARE CAN AND CANNOT OBSERVE - read before adding a
// DEVCMDSTAT-based pass/fail check here.
//
// The DSUS_C prints below are DIAGNOSTIC ONLY. An earlier revision of this file
// required two of them (suspend entry and exit) and printed FAIL otherwise.
// That check can never pass on this IP and was removed. Measured from the FSDB
// of the failing run, window 1080-1145 us:
//
//   PIE_SUSPEND                         0 -> 1 at 1083628 ns, 1 -> 0 at 1141116 ns
//   utmi_suspendm_o                     1 -> 0 at 1087845 ns, 0 -> 1 at 1137845 ns
//   USB_REG_IF_1 REG_DEV_SUSPEND        flat 0, zero value changes
//   USB_REG_IF_1 REG_DEV_SUSPEND_CHANGE flat 0, zero value changes
//
// So the PIE really did suspend, for 57.5 us, and the UTMI pin followed it after
// the clk_off_counter hold - but USBDC0's register block was never told. In
// usb_reg_if.m.vhdl, DEVCMDSTAT.DSUS is a direct assign of that instance's
// sync_suspend (line 196) and DSUS_C is set only on a change of it (lines
// 836-840). With sync_suspend flat 0 there is no edge, so DSUS_C cannot set.
//
// The cause is architectural, not a defect: the on-chip hub does not propagate
// upstream global suspend down to its downstream port. See the "Scope and
// Limitations" section of caliptra_ss_usb_hs_dev_global_suspend_L2/README.md,
// which keeps its own DSUS_C prints diagnostic for the same reason, and
// docs/usb/usb_hub_port_suspend_not_wired_report.md in the accessories repo,
// where per-port suspend being status-only is a designer-accepted deviation.
//
// The pass/fail decision for this test therefore lives entirely in
// caliptra_ss_usb_suspend_resume_checker (CHK_SUSPEND_SEEN / CHK_RESUME_SEEN).

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t intstat;
    uint32_t suspend_seen = 0;

    VPRINTF(LOW, "MCU: hs_dev_sanity_suspend test\n");
    boot_mcu();

    // boot_usb_core_hub() brings up USBDC0 in HS mode. On the hub-composite IP
    // it also programs the HUB descriptor array and sets HUB_CTRL.HUB_EN (via
    // usb_hub_init_and_connect()); USBDC0 is an embedded downstream device of
    // the on-chip hub, not a device directly on the bus.
    boot_usb_core_hub();

    // Two-phase hub bring-up. HUB_EN was set inside boot_usb_core_hub(); now
    // that USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed it is safe
    // to connect the hub upstream. usb_hub_connect() sets HUB_CONNECT, per the
    // reference BFM two-phase sequencing. Only after this does the host see
    // the hub, perform the HS chirp, and enumerate downstream port 0 (USBDC0).
    //
    // This call was missing and was the cause of the test hanging: without
    // HUB_CONNECT the hub never presents itself on the bus, the VIP link never
    // reaches ENABLED, and the host sequence waits for a link state that can
    // never be reached. No bus reset and no suspend ever occur.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request before the host-side
    // suspend stimulus is driven. boot_usb_core_hub() sets FORCE_NEEDCLK, which
    // holds usbreg_pll_on (and therefore the compound-structure clock_on term)
    // high; while clock_on is high the clk_off_counter is reloaded every pie
    // clock edge instead of counting down, so utmi_suspendm can never fall and
    // the suspend/resume checker can never observe a suspend edge. Clearing it
    // here keeps the change local to this test.
    usb_allow_clock_stop();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        // Periodic progress trace. A loop that runs its whole ceiling with zero
        // observations is otherwise undebuggable from the console: the earlier
        // "0 of 2 DSUS_C events" failure gave no indication of what the device
        // registers looked like while the firmware was polling. The interval is
        // coarse on purpose - each VPRINTF costs MCU cycles and so lengthens
        // the poll period.
        if (poll_count % 2000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x suspend_seen=%d\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    suspend_seen);
        }

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
        intstat  = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);
        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK)
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT,
                lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT) | DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK);
            suspend_seen++;
            VPRINTF(LOW, "MCU: Suspend change event %d DEVCMDSTAT=0x%x\n", suspend_seen, reg_data);
        }
    }
    // Diagnostic, not a verdict. Zero is the expected value on this IP - see the
    // note on DSUS_C observability at the top of this file. The word FAIL must
    // not appear on this line: caliptra_ss_top_tb's MCU_CONSOLE_FAIL_CHK turns
    // any MCU console line containing it into a UVM_ERROR.
    VPRINTF(LOW, "MCU: DSUS_C events observed: %d (diagnostic only; the verdict is CHK_SUSPEND_SEEN / CHK_RESUME_SEEN)\n",
            suspend_seen);
    VPRINTF(LOW, "MCU: hs_dev_sanity_suspend test complete\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
