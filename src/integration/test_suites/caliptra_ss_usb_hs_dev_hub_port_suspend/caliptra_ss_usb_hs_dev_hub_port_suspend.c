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

// Description: MCU firmware for the hub downstream PORT_SUSPEND test. Boots the
// HS device controller behind the on-chip compound hub, serves EP0 so the host
// can enumerate USBDC0, and then logs DEVCMDSTAT.DSUS_C transitions while the
// host drives SetPortFeature(PORT_SUSPEND) / ClearPortFeature(PORT_SUSPEND) on
// the hub's downstream port 1.
//
// WHAT THIS FIRMWARE DOES AND DOES NOT DO
// The port suspend request is decoded entirely in hub RTL (usb_app_hw_hub), not
// by this MCU: the hub's EP0 SETUP-match table is an RTL ROM and SetHubPortFeature
// is already in it. There is therefore no firmware register write that can make
// the downstream port suspend, and none is attempted here. This firmware is a
// passive device-side observer, exactly as in caliptra_ss_usb_hs_dev_global_suspend_L2.
//
// NO DSUS_C IS EXPECTED, AND THAT IS NOT A FAILURE
// Hub downstream port suspend is a status-only feature on this IP by design:
// the request is decoded and correctly reported in the port status word, but it
// is never propagated downstream, so the device controller never suspends and
// DSUS_C never fires. This is an accepted deviation, documented in
// docs/usb_hub_port_suspend_not_wired_report.md and README.md in this
// directory.
//
// The DSUS_C counting below is therefore pure logging, never a verdict. It is
// kept for two reasons: it makes the device-side view visible in the log next
// to the host-side status ladder, and if per-port suspend actuation is ever
// implemented this firmware already reports it without needing changes. The
// pass/fail for this test lives entirely in the UVM sequence, which checks the
// port status ladder and then proves the device still answers control traffic
// after ClearPortFeature(PORT_SUSPEND).
//
// Hub-composite IP: USBDC0 is an embedded downstream device of the on-chip
// 2-port hub, so its registers live at USB_DEV_* (base 0x20001000), not at the
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

// Safety ceiling on the DEVCMDSTAT polling loop.
//
// This is a fallback only. The normal exit path is the host-observable one
// implemented below: the firmware halts once it has served the post-resume
// GetDescriptor(Device), which is the last thing the host asks of this device.
// The ceiling exists so that a build in which that request never arrives (a
// broken link, a hub that STALLs, a sequence change) still terminates and fails
// visibly instead of hanging the regression.
//
// It must stay long enough to outlast the whole host-side ladder:
// LINK_SETTLE_DELAY (500 us) plus enumeration, PORT_SUSPEND_DWELL (600 us), the
// GetPortStatus / ClearFeature steps, POST_RESUME_SETTLE and the post-resume
// GetDescriptor. Serving EP0 to the end matters more here than in most tests,
// because the final host-side check is a control transfer to this device: if the
// MCU halted early that check would fail for a firmware reason rather than a
// design one. The same value as the global_suspend_L2 test is reused, which
// covers a comparable stimulus length there.
//
// Nothing can finish the run while the MCU is alive: caliptra_ss_usb_base_test
// holds a run_phase objection in mcu_halt_monitor_task() until this function
// reaches csr_write_mpmc_halt(). Reaching the ceiling therefore costs real
// wall-clock regression time, which is why it is no longer the normal path.
#define USB_POLL_TIMEOUT 50000

// Which GetDescriptor(Device) after SET_ADDRESS(2) is the post-resume check.
//
// The host-side ladder issues exactly two device-descriptor reads at the
// assigned address: the first closes enumeration (GET_DESC_DEV_addr2 inside
// usbdc0_enum_stepC), the second is post_resume_traffic_check() after
// ClearFeature(PORT_SUSPEND). Descriptor reads before SET_ADDRESS(2) are not
// counted, so the earlier addr-0 read during enumeration cannot be mistaken for
// either of these. Counting requests rather than waiting a fixed time is what
// makes this exit deterministic: it does not shift if host-side delays change.
//
// If the sequence is ever extended to read the device descriptor again after the
// post-resume check, this value must be raised to match, otherwise the firmware
// will halt before the later transfer and that transfer will fail.
#define USB_POSTRESUME_DESC_COUNT 2

// Extra polls served after the post-resume descriptor request is answered,
// before halting.
//
// usb_handle_control_transfer() arms the IN data phase and the OUT status phase
// before returning, so the transfer is already complete from the firmware side.
// This window only covers the tail of that transfer on the wire plus the
// sequence's own trailing settle, so the run is never cut off mid-transfer. It
// is small: the point of this change is that the firmware stops spinning once
// there is nothing left to serve.
#define USB_POST_CHECK_GRACE_POLLS 500

// Number of DSUS_C events after which the log loop stops early: one for entering
// suspend, one for leaving. On this IP neither occurs, so this is only an upper
// bound on logging, not an expectation. It is deliberately not named EXPECTED.
#define USB_DSUS_EVENTS_LOG_LIMIT 2



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

    // Host-progress tracking, used only to decide when there is nothing left to
    // serve so the firmware can halt. None of this is a pass or fail; the
    // verdict lives in the UVM sequence.
    bool     addr_assigned  = false;  // SET_ADDRESS(2) has been served
    uint32_t dev_desc_reads = 0;      // GetDescriptor(Device) reads at addr 2
    bool     check_done     = false;  // post-resume descriptor read served
    uint32_t grace_polls    = 0;      // polls served since check_done

    VPRINTF(LOW, "MCU: hs_dev_hub_port_suspend test\n");
    boot_mcu();

    // boot_usb_core() brings up USBDC0 in HS mode. On the hub-composite IP it
    // also programs and validates the HUB descriptor RAM and sets HUB_EN (via
    // usb_hub_init_and_connect()); USBDC0 is an embedded downstream device of
    // the on-chip hub, not a device directly on the bus.
    boot_usb_core();

    // Two-phase hub bring-up: HUB_EN was set inside boot_usb_core(); now that
    // USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed it is safe to
    // connect the hub upstream. usb_hub_connect() sets HUB_CONNECT. Only after
    // this does the host see the hub, perform HS chirp, and enumerate the
    // downstream port. Without it the upstream link never reaches ENABLED, and
    // the hub-class port requests this test exists to drive would have nowhere
    // to go.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();

    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request. boot_usb_core() sets
    // FORCE_NEEDCLK, which holds usbreg_pll_on (and therefore the
    // compound-structure clock_on term) high; while clock_on is high,
    // clk_off_counter is reloaded to CLOCKOFF_CYCLE every pie_clk edge instead
    // of counting down, so utmi_suspendm can never fall.
    //
    // Nothing in this test depends on utmi_suspendm any more, so this call is
    // not load bearing here. It is kept so that the device is left in the same
    // state as in the global_suspend_L2 tests, i.e. so that a suspend would be
    // observable at the pins if per-port actuation is ever implemented, without
    // this precondition having to be rediscovered. Harmless either way. See
    // docs/usb_remote_wakeup_debug.md.
    usb_allow_clock_stop();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();

                // Classify the request that was just served, to know when the
                // host has finished with this device.
                //
                // Deliberately done AFTER the handler returns, not before. The
                // handler must arm EP0 IN within a few microseconds of the
                // SETUP-ACK or the host VIP gives up on polling IN (see the
                // hot-path notes in libs/usb/usb.c), so nothing is inserted
                // ahead of it. The SETUP buffer in SRAM is not consumed by the
                // handler, so re-reading it here yields the same packet.
                usb_setup_pkt_t pkt;
                usb_read_setup_packet(&pkt);

                if (USB_BMREQTYPE_TYPE(pkt.bmRequestType) == USB_TYPE_STANDARD &&
                    USB_BMREQTYPE_RECIPIENT(pkt.bmRequestType) == USB_RECIP_DEVICE) {

                    if (pkt.bRequest == USB_REQ_SET_ADDRESS &&
                        (pkt.wValue & 0x7Fu) != 0u) {
                        // Enumeration has assigned the address. Descriptor
                        // reads from here on are the ones being counted.
                        addr_assigned = true;
                    }
                    else if (pkt.bRequest == USB_REQ_GET_DESCRIPTOR &&
                             ((pkt.wValue >> 8) & 0xFFu) == USB_DESC_DEVICE &&
                             addr_assigned) {
                        dev_desc_reads++;
                        if (!check_done &&
                            dev_desc_reads >= USB_POSTRESUME_DESC_COUNT) {
                            check_done = true;
                            VPRINTF(LOW, "MCU: post-resume GetDescriptor(Device) served (device-descriptor read %d at the assigned address) after %d polls; host-side checks are complete, halting shortly\n",
                                    dev_desc_reads, poll_count + 1);
                        }
                    }
                }
            }
        }
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        if (reg_data & USBHSD_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is write-1-to-clear. Read-modify-write of the live value
            // rather than reg_data so that no other status bit that changed in
            // the meantime is clobbered.
            lsu_write_32(USB_DEV_DEVCMDSTAT,
                lsu_read_32(USB_DEV_DEVCMDSTAT) | USBHSD_DEVCMDSTAT_DSUS_C_MASK);

            suspend_seen++;
            VPRINTF(LOW, "MCU: Suspend change event %d DEVCMDSTAT=0x%x\n", suspend_seen, reg_data);

            if (suspend_seen >= USB_DSUS_EVENTS_LOG_LIMIT) {
                VPRINTF(LOW, "MCU: both DSUS_C events observed after %d polls; ending poll loop\n",
                        poll_count + 1);
                break;
            }
        }

        // Normal exit. The host has nothing further to ask of this device, so
        // spinning to the ceiling would only burn simulation time while holding
        // the base test's run_phase objection.
        if (check_done) {
            if (grace_polls >= USB_POST_CHECK_GRACE_POLLS) {
                VPRINTF(LOW, "MCU: grace window of %d polls served after the post-resume check; ending poll loop at poll %d\n",
                        USB_POST_CHECK_GRACE_POLLS, poll_count + 1);
                break;
            }
            grace_polls++;
        }
    }

    // Logged, never a firmware-side pass or fail. On this IP the count is 0,
    // which is the correct and accepted behaviour: per-port suspend is not
    // actuated. The line exists so the device-side view is on record next to the
    // host-side status ladder in the same log.
    if (suspend_seen < USB_DSUS_EVENTS_LOG_LIMIT)
        VPRINTF(LOW, "MCU: ending with %d of %d DSUS_C events; 0 is expected because hub port suspend is status-only on this IP, see docs/usb_hub_port_suspend_not_wired_report.md\n",
                suspend_seen, USB_DSUS_EVENTS_LOG_LIMIT);

    // Distinguish the normal exit from the fallback. Reaching the ceiling means
    // the post-resume GetDescriptor(Device) never arrived, so the host-side
    // check that this firmware exists to support cannot have passed. That is
    // reported here as a warning because the verdict itself belongs to the UVM
    // sequence, which will have flagged the missing transfer as an error.
    if (!check_done)
        VPRINTF(LOW, "MCU: WARNING poll ceiling of %d reached without serving the post-resume GetDescriptor(Device) (%d device-descriptor reads at the assigned address, address assigned=%d). The host-side post-resume check cannot have passed; see the UVM sequence errors in this log.\n",
                USB_POLL_TIMEOUT, dev_desc_reads, (int)addr_assigned);

    VPRINTF(LOW, "MCU: hs_dev_hub_port_suspend test complete\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
