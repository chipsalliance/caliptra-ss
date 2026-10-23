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
// as both suspend-change events have been observed, so this value is only paid
// when the DUT never completes the suspend/resume cycle.
#define USB_POLL_TIMEOUT 50000

// Number of DEVCMDSTAT.DSUS_C events this firmware exists to observe: one on
// suspend entry, one on resume. Once both are logged the MCU halts, releasing
// the base test's run_phase objection. Same value and rationale as the twin
// caliptra_ss_usb_hs_dev_global_suspend_L2.
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

    // boot_usb_core_hub() brings up USBDC0 in HS mode and, on the hub-composite
    // IP, programs the HUB descriptor RAM and sets HUB_EN. USBDC0 is an embedded
    // downstream device of the on-chip hub, not a device directly on the bus.
    boot_usb_core_hub();

    // Two-phase hub bring-up: HUB_EN was set inside boot_usb_core_hub(); now that
    // USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed it is safe to
    // connect the hub upstream. usb_hub_connect() sets HUB_CONNECT. Only after
    // this does the host see the hub, perform HS chirp, and enumerate its
    // downstream port 0 (USBDC0). Without it the upstream link never reaches
    // ENABLED, so the host sequence blocks forever waiting on the link state and
    // the simulation never terminates (the test shows up as neither PASS nor
    // FAIL). This mirrors the twin caliptra_ss_usb_hs_dev_global_suspend_L2.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request before the host-side suspend
    // stimulus is armed. boot_usb_core_hub() sets FORCE_NEEDCLK, which holds
    // usbreg_pll_on (and the compound clock_on term) high; while clock_on is
    // high, clk_off_counter is reloaded every pie_clk edge instead of counting
    // down, so utmi_suspendm can never fall and no suspend edge is ever
    // observed. Same requirement and rationale as the global_suspend_L2 twin.
    // See docs/usb_remote_wakeup_debug.md.
    usb_allow_clock_stop();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);
        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is write-1-to-clear. Read-modify-write of the live value
            // rather than reg_data so that no other status bit that changed in
            // the meantime is clobbered.
            lsu_write_32(USB_DEV_DEVCMDSTAT,
                lsu_read_32(USB_DEV_DEVCMDSTAT) | DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK);
            suspend_seen++;
            VPRINTF(LOW, "MCU: Suspend change event %d DEVCMDSTAT=0x%x\n", suspend_seen, reg_data);

            // Both halves of the suspend/resume cycle have been observed, so the
            // firmware has nothing left to contribute. Stop polling: the base
            // test's run_phase objection is only released once this function
            // halts the MCU, so spinning to the ceiling would only hold the
            // simulation open. The UVM sequence owns its own objection, so its
            // checks are unaffected. Same early-exit as the global_suspend_L2
            // twin.
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
