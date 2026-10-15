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
// on-chip compound hub, FULL SPEED.
//
// The MCU is the agent that ends the suspend here: it waits for the controller
// to report itself suspended, then calls usb_request_remote_wakeup() so USBDC0
// drives resume K upstream. The verdict is CHK_DEVICE_WAKEUP_K in
// caliptra_ss_usb_device_wakeup_checker, not anything this file prints.
//
// Design notes, the pie resume timeline, the register-access conventions and the
// poll-constant derivations all live in a single note. Read it before changing
// anything here:
//   caliptra_ss_nxp_dv_accessories/docs/handover/claude_md/
//       25_usb_remotewakeup_fromdevice_design_notes.md
// The HS port of this firmware is note 24 of the same directory.

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

// Ceiling on the DEVCMDSTAT polling loop, not a dwell: the loop exits as soon as
// the whole suspend -> wakeup -> resume cycle has been observed. ~12 ms at the
// measured ~80 ns per iteration, and it must stay above the poll index at which
// the grace window below expires (~107700). Note 25 section 8.
#define USB_POLL_TIMEOUT 150000

// How long to stay suspended before asking for the wakeup, in poll iterations
// (~80 ns each, so ~80 us). Must not pre-empt the SuspendM falling edge the
// checker scores as CHK_SUSPEND_SEEN. Note 25 section 8.
#define USB_WAKEUP_ARM_DELAY_POLLS 1000

// Grace window kept running after the resume so the sequence's post-resume
// GET_DESCRIPTOR(DEVICE) still finds EP0 served. ~5.6 ms; must stay longer than
// POST_RESUME_SETTLE (3.5 ms here) in the sequence. Note 25 section 8.
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

    // FS boot entry point: sets DEVCMDSTAT FORCE_FULLSPEED to suppress the
    // device-side K-chirp, which is correct only against the FS-only VIP this
    // test configures. It also programs the HUB descriptor RAM and sets HUB_EN.
    // Note 25 section 8.
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
    // Load-bearing: with FORCE_NEEDCLK still set, utmi_suspendm never falls and
    // there is no suspended state to wake from. Note 25 section 8.
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

        // Note the prefix split in the two macro families used below: the
        // register ADDRESSES are the device-neutral USB_DEV_* macros, while the
        // bitfield MASKS are DEV0_CSR_*. That is the documented convention, see
        // libs/usb/usb.h: soc_address_map.h only generates the DEV0_CSR_*
        // MASK/SHIFT macros, and those masks are offset-independent within a CSR
        // bank, so they apply verbatim to USBDC0 and USBDC1 alike. USB_DEV_SEL
        // parametrizes the addresses only.
        if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        // EP0 IN completion needs no action: the ISR already acknowledged it.

        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is write-1-to-clear. Read-modify-write of the live value
            // rather than reg_data so that no other status bit that changed in
            // the meantime is clobbered. Note the wakeup request below performs
            // its own DSUS_C acknowledge, which is why the entry edge is only
            // acked here when the wakeup has not been armed yet.
            if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) {
                if (!suspend_seen) {
                    suspend_seen = 1;
                    suspend_entry_poll = poll_count;
                    VPRINTF(LOW, "MCU: suspend entered at poll %d DEVCMDSTAT=0x%x\n",
                            poll_count, reg_data);
                }
                lsu_write_32(USB_DEV_DEVCMDSTAT,
                    lsu_read_32(USB_DEV_DEVCMDSTAT) | DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK);
            } else {
                // DSUS is now 0 with a change flagged: the controller has left
                // suspend. This is the register-side confirmation that the
                // wakeup this firmware requested actually took effect.
                lsu_write_32(USB_DEV_DEVCMDSTAT,
                    lsu_read_32(USB_DEV_DEVCMDSTAT) | DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK);
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
                // real ordering problem behind a loop, and the DUT-side
                // CHK_DEVICE_WAKEUP_K check will report the missing wakeup.
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
