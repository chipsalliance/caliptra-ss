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

// Description: USB HS device suspend/resume observation firmware. Boots the HS
// device controller behind the on-chip compound hub, handles EP0 enumeration,
// and monitors DEVCMDSTAT.DSUS_C to log suspend and resume change events.
//
// Note on the test name: the resume is driven by the HOST in the UVM sequence
// (svt_usb_link_service_clear_suspend_sequence). This firmware does not itself
// initiate remote wakeup upstream; it only observes the suspend-change status
// bit. See README.md "Scope and limitations".
//
// Hub-composite IP: USBDC0 is an embedded downstream device of the on-chip
// 2-port hub, so its registers live at USB_DEV0_* (base 0x20001000), not at the
// legacy SOC_USBHSD_* base, and the hub must be connected upstream by firmware
// before the host can see anything.


#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Ceiling on the DEVCMDSTAT polling loop, not a dwell. The loop exits as soon
// as both suspend-change events have been observed (see USB_DSUS_EVENTS_EXPECTED
// below), so this value is only paid when the DUT never completes the cycle.
#define USB_POLL_TIMEOUT 50000

// Number of DEVCMDSTAT.DSUS_C events that constitute the whole observation this
// firmware exists to make: one when the device controller enters suspend, one
// when it leaves. Once both have been logged there is nothing further for the
// MCU to do, so it halts.
//
// Why this matters for runtime. Nothing in the testbench can finish the
// simulation while the MCU is still running: caliptra_ss_usb_base_test holds a
// run_phase objection in mcu_halt_monitor_task() until cptra_ss_mcu_halt_status_o
// asserts, which only happens when this function reaches csr_write_mpmc_halt().
// Running the full USB_POLL_TIMEOUT iterations after the DUT has already been
// observed therefore extends the simulation by a large amount of wall time
// without adding a single observation. Exiting on the event count instead makes
// the loop end because the DUT completed the cycle, rather than because a
// counter ran out.
#define USB_DSUS_EVENTS_EXPECTED 2


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

    VPRINTF(LOW, "MCU: hs_dev_remote_wakeup test\n");
    boot_mcu();

    // boot_usb_core() brings up USBDC0 in HS mode. On the hub-composite IP it
    // also programs and validates the HUB descriptor RAM and sets HUB_EN (via
    // usb_hub_init_and_connect()); USBDC0 is an embedded downstream device of
    // the on-chip hub, not a device directly on the bus.
    boot_usb_core();

    // Two-phase hub bring-up: HUB_EN was set inside boot_usb_core(); now that
    // USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed it is safe to
    // connect the hub upstream. usb_hub_connect() sets HUB_CONNECT, per the
    // reference janus_hub_ctrl_bfm.sv two-phase sequencing. Only after this
    // does the host see the hub, perform HS chirp, and enumerate its
    // downstream port 0 (USBDC0). Without it the upstream link never reaches
    // ENABLED and the host sequence cannot suspend anything.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();

    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request before the host-side
    // suspend stimulus is armed. boot_usb_core() sets FORCE_NEEDCLK, which
    // holds usbreg_pll_on (and therefore the compound-structure clock_on
    // term) high; while clock_on is high, clk_off_counter is reloaded to
    // CLOCKOFF_CYCLE every pie_clk edge instead of counting down, so
    // utmi_suspendm can never fall and the suspend/resume checker never
    // observes a suspend edge. Clearing the bit here keeps the change local
    // to this test - the other USB tests still rely on FORCE_NEEDCLK during
    // their bring-up. See docs/usb_remote_wakeup_debug.md.
    usb_allow_clock_stop();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV0_INTSTAT);
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        if (reg_data & USBHSD_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is write-1-to-clear. Read-modify-write of the live value
            // rather than reg_data so that no other status bit that changed in
            // the meantime is clobbered.
            lsu_write_32(USB_DEV0_DEVCMDSTAT,
                lsu_read_32(USB_DEV0_DEVCMDSTAT) | USBHSD_DEVCMDSTAT_DSUS_C_MASK);

            suspend_seen++;
            VPRINTF(LOW, "MCU: Suspend change event %d DEVCMDSTAT=0x%x\n", suspend_seen, reg_data);

            // Both halves of the suspend/resume cycle have now been observed
            // from the register side, so this firmware has nothing left to
            // contribute. Stop polling: the run_phase objection in
            // caliptra_ss_usb_base_test is only released once this function
            // halts the MCU, so continuing to spin here would hold the whole
            // simulation open for no additional coverage.
            //
            // This does not shorten the host-side stimulus. The UVM sequence
            // owns its own objection and closes the checker observation window
            // (usb_suspend_resume_obs_window_done) independently, so
            // CHK_SUSPEND_SEEN and CHK_RESUME_SEEN are still evaluated exactly
            // as before; the MCU simply stops being the last thing holding the
            // run phase.
            if (suspend_seen >= USB_DSUS_EVENTS_EXPECTED) {
                VPRINTF(LOW, "MCU: both DSUS_C events observed after %d polls; ending poll loop\n",
                        poll_count + 1);
                break;
            }
        }
    }
    if (suspend_seen < USB_DSUS_EVENTS_EXPECTED)
        VPRINTF(LOW, "MCU: poll ceiling reached with only %d of %d DSUS_C events\n",
                suspend_seen, USB_DSUS_EVENTS_EXPECTED);
    VPRINTF(LOW, "MCU: hs_dev_remote_wakeup test complete\n");
    csr_write_mpmc_halt();
}
