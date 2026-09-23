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

// Description: device-initiated remote wakeup firmware for USBDC0 behind the
// on-chip compound hub, full speed.
//
// This is the firmware half of caliptra_ss_usb_fs_host_remotewakeup_fromdevice.
// Unlike the *_global_suspend_L2 family, where the host drives the resume and
// this side only observes the suspend-change bit, here the MCU is the agent
// that ends the suspend: it waits for the controller to report itself
// suspended, then asks the device controller to drive resume K upstream by
// calling usb_request_remote_wakeup(). The host VIP is expected to observe that
// K on the bus and complete the resume; the UVM sequence checks exactly that
// (svt_usb_status::device_remote_wakeup_in_progress) and deliberately does not
// drive a host resume of its own, so if this firmware fails to trigger the
// wakeup the test fails rather than silently passing.
//
// History: the previous version of this file used boot_usb_core() and the
// legacy SOC_USBHSD_* register base, never called usb_hub_connect(), and tried
// to trigger the wakeup with a plain read-modify-write OR of DSUS_C|DRES_C.
// None of that can work on this IP:
//   - USBDC0 is an embedded downstream device of the on-chip 2-port hub, so its
//     registers live at USB_DEV_* (base 0x20001000), and the host cannot see
//     anything at all until firmware sets HUB_CONNECT.
//   - the wakeup trigger is a write to DEVCMDSTAT with bit 17 (DSUS) driven to
//     0 while suspended; an OR read-modify-write writes DSUS back as 1 because
//     that is how it reads while suspended, so the RTL condition is never met.
//     usb_request_remote_wakeup() implements the correct masked write.
// The whole file was rewritten on the caliptra_ss_usb_fs_dev_global_suspend_L2
// pattern for that reason.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"
// Including mcu_isr.h is what makes the build system compile and link
// mcu_isr.o for this test (see tools/scripts/Makefile).
#include "mcu_isr.h"

// Ceiling on the DEVCMDSTAT polling loop, not a dwell. The loop exits as soon
// as the whole suspend -> remote-wakeup -> resume cycle has been observed, so
// this value is only paid when the DUT never completes it.
//
// Sized for full speed, same reasoning as caliptra_ss_usb_fs_dev_global_suspend_L2:
// the suspend idle interval is shortened for simulation to about 200 us at high
// speed but is still about 1.1 ms at full speed, and this loop must additionally
// cover the wakeup arming delay below, the upstream K, and the resume recovery
// interval before the second DSUS_C edge appears. At the measured ~80 ns per
// iteration 150000 iterations is roughly 12 ms, which covers all of that with
// margin while still bounding a DUT that never resumes.
//
// It must also be larger than the poll index at which the grace window below
// expires, or the ceiling would cut the grace window short. Measured: resume is
// observed at 3.017 ms, poll ~37700, plus USB_POST_RESUME_GRACE_POLLS = 70000
// puts the normal exit at ~107700, inside this 150000 ceiling. Raise this if the
// grace window is raised again.
#define USB_POLL_TIMEOUT 150000


// How long to stay suspended before asking for the wakeup, expressed in poll
// iterations (~80 ns each, so ~1000 iterations is on the order of 80 us).
//
// Two reasons this is not zero. First, USB 2.0 section 7.1.7.7 requires a
// device to stay idle for at least 5 ms before it may signal remote wakeup;
// simulation compresses that, but issuing the request in the very same poll
// iteration that first saw DSUS_C would have the device drive K while the host
// side is still settling into suspend, which is not the scenario being
// verified. Second, the checker (usb_suspend_resume_checker) scores
// CHK_SUSPEND_SEEN on the falling edge of cptra_ss_usb_utmi_suspendm_o; that
// edge follows the controller reporting DSUS by the compound-structure
// clk_off_counter countdown, so the wakeup must not pre-empt it or the suspend
// half of the check never happens and the test would be measuring a resume
// that had nothing to resume from.
#define USB_WAKEUP_ARM_DELAY_POLLS 1000

// Grace window kept running after the resume has been fully observed, so the
// UVM sequence has room to complete its post-resume control transfer while the
// MCU is still able to service EP0. The sequence issues one
// GET_DESCRIPTOR(DEVICE) after the resume to prove the device is functional
// again; if the MCU halted the instant it saw the resume edge, that transfer
// would find nobody serving EP0.
//
// Sized against the RTL and against the sequence, not chosen empirically.
// Two facts set the lower bound:
//
//   1. This window STARTS EARLY. resume_seen is taken from DEVCMDSTAT DSUS
//      falling, and DSUS is pie_suspend, which is asserted in exactly one pie
//      state, BUS_EVENT_SUSPEND (usb_pie.m.vhdl:2112-2116). The wakeup request
//      leaves that state immediately, so DSUS drops at the START of resume
//      signalling, not at the end of it. Measured: request and DSUS drop at
//      3.017 ms.
//   2. The device then drives resume K for T_3ms = 184320 pie_clk cycles
//      (usb_pie.m.vhdl:477, 1659-1663). T_3ms has NO _SIM variant, so it is not
//      compressed for simulation. Measured: pie_clk 16.76 ns, K held 3.089 ms,
//      ending at 6.106 ms, plus T_TxENDDELAY (30 us) = 6.136 ms.
//
// The sequence therefore waits POST_RESUME_SETTLE = 3.5 ms from its own resume
// observation before issuing GET_DESCRIPTOR(DEVICE), which lands at about
// 6.52 ms. This window must still be open then. At the measured ~80 ns per poll
// iteration, 20000 iterations was only 1.6 ms and expired at about 4.6 ms,
// while the device was still mid-K, so the MCU halted roughly 2 ms before the
// transfer arrived. 70000 iterations is about 5.6 ms, which covers the 3.5 ms
// settle plus the control transfer with roughly 2 ms of margin.
//
// Do not reduce this below POST_RESUME_SETTLE in
// caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence.svh, and if that
// constant is raised, raise this with it.
#define USB_POST_RESUME_GRACE_POLLS 70000


volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

// Storage for the symbols the ISR library declares extern.
volatile uint32_t intr_count;
volatile mcu_intr_received_s mcu_intr_rcv = {0};

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t usb_events;
    uint32_t suspend_entry_poll = 0;
    uint32_t resume_poll        = 0;
    uint32_t grace_polls        = 0;
    int      suspend_seen       = 0;
    int      wakeup_requested   = 0;
    int      resume_seen        = 0;

    VPRINTF(LOW, "MCU: fs_host_remotewakeup_fromdevice test\n");
    boot_mcu();

    // boot_usb_core_fs() brings up USBDC0 at full speed. On the hub-composite
    // IP it also programs and validates the HUB descriptor RAM and sets HUB_EN
    // (via usb_hub_init_and_connect()).
    boot_usb_core_fs();

    // Enable the USB interrupt (PIC vector 3) now that boot_usb_core_fs() has
    // programmed INTEN and cleared any stale INTSTAT bits. Deliberately not
    // init_interrupts(): that routine also writes the MCI and I3C interrupt
    // registers, and this early the I3C write does not complete, stalling the
    // LSU pipeline before mstatus.MIE is set.
    intr_count = 0;
    init_usb_interrupts();

    // Second phase of hub bring-up: HUB_EN was set inside boot_usb_core_fs();
    // now that USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed it is
    // safe to connect the hub upstream. Only after HUB_CONNECT does the host
    // see the hub, reset it, and enumerate downstream port 0 (USBDC0).
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();

    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request before the host stops SOF.
    // boot_usb_core_fs() sets FORCE_NEEDCLK, which holds usbreg_pll_on high;
    // while that is high, clk_off_counter is reloaded every pie_clk edge
    // instead of counting down, so utmi_suspendm can never fall, the
    // controller never reports DSUS, and there is no suspended state from
    // which to request a remote wakeup. See docs/usb_remote_wakeup_debug.md.
    usb_allow_clock_stop();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);

        // Drain the ISR mailbox. service_usb_intr() already read and
        // acknowledged INTSTAT, so the foreground loop must not touch INTSTAT
        // itself. Snapshot then clear by complement so bits the ISR sets while
        // we are handling this batch are not lost. DEVCMDSTAT is still read
        // directly above: DSUS/DSUS_C are DEVCMDSTAT bits, not INTSTAT bits,
        // so they do not travel through the mailbox.
        usb_events = mcu_intr_rcv.usb;
        mcu_intr_rcv.usb &= ~usb_events;

        if (usb_events & USBHSD_INTSTAT_EP0OUT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        // EP0 IN completion needs no action: the ISR already acknowledged it.

        if (reg_data & USBHSD_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is write-1-to-clear. Read-modify-write of the live value
            // rather than reg_data so that no other status bit that changed in
            // the meantime is clobbered. Note the wakeup request below performs
            // its own DSUS_C acknowledge, which is why the entry edge is only
            // acked here when the wakeup has not been armed yet.
            if (reg_data & USBHSD_DEVCMDSTAT_DSUS_MASK) {
                if (!suspend_seen) {
                    suspend_seen = 1;
                    suspend_entry_poll = poll_count;
                    VPRINTF(LOW, "MCU: suspend entered at poll %d DEVCMDSTAT=0x%x\n",
                            poll_count, reg_data);
                }
                lsu_write_32(USB_DEV_DEVCMDSTAT,
                    lsu_read_32(USB_DEV_DEVCMDSTAT) | USBHSD_DEVCMDSTAT_DSUS_C_MASK);
            } else {
                // DSUS is now 0 with a change flagged: the controller has left
                // suspend. This is the register-side confirmation that the
                // wakeup this firmware requested actually took effect.
                lsu_write_32(USB_DEV_DEVCMDSTAT,
                    lsu_read_32(USB_DEV_DEVCMDSTAT) | USBHSD_DEVCMDSTAT_DSUS_C_MASK);
                if (!resume_seen) {
                    resume_seen = 1;
                    resume_poll = poll_count;
                    VPRINTF(LOW, "MCU: resume observed at poll %d DEVCMDSTAT=0x%x\n",
                            poll_count, reg_data);
                }
            }
        }

        // Arm the wakeup once the controller has been suspended long enough.
        // usb_request_remote_wakeup() re-reads DEVCMDSTAT and refuses if DSUS
        // is no longer set, so a resume that arrives from the host in the
        // meantime cannot turn this into a spurious request.
        if (suspend_seen && !wakeup_requested && !resume_seen &&
            (poll_count - suspend_entry_poll) >= USB_WAKEUP_ARM_DELAY_POLLS) {
            if (usb_request_remote_wakeup()) {
                wakeup_requested = 1;
                VPRINTF(LOW, "MCU: remote wakeup driven at poll %d\n", poll_count);
            } else {
                // Not suspended any more. Do not retry: retrying would hide a
                // real ordering problem behind a loop, and the sequence-side
                // check on device_remote_wakeup_in_progress will report the
                // missing wakeup.
                wakeup_requested = 1;
                VPRINTF(LOW, "MCU: remote wakeup request refused at poll %d (not suspended)\n",
                        poll_count);
            }
        }

        // Everything this firmware exists to do has happened. Keep serving EP0
        // for a bounded grace window so the sequence's post-resume control
        // transfer can complete, then stop. Nothing in the testbench can end
        // the simulation while the MCU runs: caliptra_ss_usb_base_test holds a
        // run_phase objection in mcu_halt_monitor_task() until
        // cptra_ss_mcu_halt_status_o asserts, which only happens once this
        // function reaches csr_write_mpmc_halt(). Spinning to USB_POLL_TIMEOUT
        // after the observation is complete would add wall-clock time and no
        // coverage.
        if (resume_seen && wakeup_requested) {
            if (++grace_polls >= USB_POST_RESUME_GRACE_POLLS) {
                VPRINTF(LOW, "MCU: post-resume grace window complete at poll %d; ending poll loop\n",
                        poll_count);
                break;
            }
        }
    }

    if (!suspend_seen)
        VPRINTF(LOW, "MCU: ERROR poll ceiling reached without entering suspend\n");
    else if (!wakeup_requested)
        VPRINTF(LOW, "MCU: ERROR poll ceiling reached without arming remote wakeup\n");
    else if (!resume_seen)
        VPRINTF(LOW, "MCU: ERROR poll ceiling reached without observing resume\n");
    else
        VPRINTF(LOW, "MCU: suspend at poll %d, resume at poll %d\n",
                suspend_entry_poll, resume_poll);

    VPRINTF(LOW, "MCU: fs_host_remotewakeup_fromdevice test complete\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
