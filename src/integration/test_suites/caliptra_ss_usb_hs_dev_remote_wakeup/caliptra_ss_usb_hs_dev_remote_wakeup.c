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

// Description: USB HS device remote wakeup firmware. Boots HS device, handles EP0 enumeration, detects suspend (DSUS), drives remote wakeup by clearing DSUS and toggling device resume signaling. Monitors DSUS_C.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Ceiling on the DEVCMDSTAT polling loop, not a dwell. The loop exits as soon
// as both suspend-change events have been observed (see
// USB_DSUS_EVENTS_EXPECTED), so this value is only paid when the DUT never
// completes the cycle.
#define USB_POLL_TIMEOUT 18000

// Number of DEVCMDSTAT.DSUS_C events that constitute the whole observation this
// firmware exists to make: one when the device controller enters suspend, one
// when it leaves. Once both have been logged there is nothing further for the
// MCU to do, so it halts.
//
// Why this matters for runtime: nothing in the testbench can finish the
// simulation while the MCU is still running, because caliptra_ss_usb_base_test
// holds a run_phase objection until cptra_ss_mcu_halt_status_o asserts, which
// only happens when this function reaches csr_write_mpmc_halt(). Spinning out
// the full USB_POLL_TIMEOUT after the DUT has already been observed costs a
// large amount of wall time and adds no observation.
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

            // Both halves of the suspend/resume cycle have now been observed
            // from the register side, so this firmware has nothing left to
            // contribute. Stopping here releases the MCU-halt objection that
            // otherwise holds the whole simulation open. It does not shorten
            // the host-side stimulus: the UVM sequence owns its own objection
            // and closes the checker observation window independently, so
            // CHK_SUSPEND_SEEN and CHK_RESUME_SEEN are still evaluated.
            if (suspend_seen >= USB_DSUS_EVENTS_EXPECTED) {
                VPRINTF(LOW, "MCU: both DSUS_C events observed after %d polls; ending poll loop\n",
                        poll_count + 1);
                break;
            }
        }
    }
    if (suspend_seen < USB_DSUS_EVENTS_EXPECTED)
        VPRINTF(LOW, "MCU: FAIL - poll ceiling reached with only %d of %d DSUS_C events\n",
                suspend_seen, USB_DSUS_EVENTS_EXPECTED);
    VPRINTF(LOW, "MCU: hs_dev_remote_wakeup test complete\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
