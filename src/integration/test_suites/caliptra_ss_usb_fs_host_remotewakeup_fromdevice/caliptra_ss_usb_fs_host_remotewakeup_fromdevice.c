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

// Ceiling on the DEVCMDSTAT polling loop, not a dwell: the loop exits as soon
// as the suspend -> wakeup -> resume cycle has been observed, via the grace
// window below. This is only a backstop against a run where the cycle never
// completes, so its whole cost is paid on FAILING runs.
//
// The iteration rate was MEASURED on a passing run rather than estimated:
// suspend at poll 19950 / 2664175 ns and the wakeup at poll 20950 / 2795045 ns
// give 1000 polls = 130870 ns, i.e. ~131 ns per poll. An earlier comment here
// claimed ~80 ns and a grace expiry at ~107700; both were wrong by ~1.6x,
// which is how 150000 came to be ~19.6 ms of ceiling instead of the ~12 ms it
// was believed to be.
//
// At ~131 ns, 80000 polls is ~10.5 ms. A healthy run leaves the loop via the
// grace window at roughly 19950 + 1000 + 40000 = ~61000, so this ceiling is
// never the exit path; the ~30% headroom is there because the MCU clock is
// randomised 333/400 MHz (see note 11), and at the slower clock the same bus
// instant lands ~1.2x later in polls (~65000). Do not trim it below that.
#define USB_POLL_TIMEOUT 80000

// How long to stay suspended before asking for the wakeup, in poll iterations
// (~131 ns each, so ~131 us). Must not pre-empt the SuspendM falling edge the
// checker scores as CHK_SUSPEND_SEEN.
#define USB_WAKEUP_ARM_DELAY_POLLS 1000

// Consecutive polls on which DSUS must read 1 before the wakeup command is
// issued. The delay above counts polls since this firmware first noticed
// suspend, which says nothing about whether the controller has finished
// entering it; requiring a stable DSUS as well means the command cannot land
// in a suspend-entry transition.
#define USB_WAKEUP_STABLE_DSUS_POLLS 4

// Bounded retries for the wakeup command. usbreg_remotewakeup is raised by a
// DEVCMDSTAT write presenting DSUS as 0 while suspended; it is a command, not
// a latched bit, so a write the controller does not act on leaves no trace and
// cannot be recovered except by issuing it again. A nightly run showed the
// command correctly formed and accepted (usb_request_remote_wakeup() returned
// true) with DSUS still 1 afterwards and no resume K ever driven, i.e. the
// controller silently ignored it. Retry a few times, then fail loudly naming
// the register rather than letting the UVM checker report a bare missing K
// several hundred microseconds later.
#define USB_WAKEUP_MAX_ATTEMPTS 3

// Polls to wait after a wakeup command before judging whether it took effect.
// The controller must restart its clock and drive K upstream; ~260 us at
// ~131 ns per poll is far longer than that needs, and still well inside the
// sequence's device-K ceiling.
#define USB_WAKEUP_VERIFY_POLLS 2000


// Grace window kept running after the resume so the sequence's post-resume
// GET_DESCRIPTOR(DEVICE) still finds EP0 served. Must stay longer than
// POST_RESUME_SETTLE in the sequence (3.5 ms at FS).
//
// Sized from measurement, and this is the DOMINANT term in the loop budget, so
// it sets the simulated length of a PASSING run too. On the passing run the
// resume was observed at 2797225 ns and the post-resume GetDescriptor was
// served at 6324830 ns, i.e. 3.53 ms or ~27000 polls at the measured ~131 ns;
// call it ~28000 to the transfer completing. 40000 polls is ~5.2 ms, leaving
// ~43% margin, against the 70000 (~9.2 ms) this was previously set to.
//
// If this window ever truncates, the firmware stops serving EP0 mid-window and
// the sequence's GetDescriptor times out looking exactly like a DUT fault, so
// raise this before suspecting the DUT.
#define USB_POST_RESUME_GRACE_POLLS 40000


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
    uint32_t dsus_stable_polls  = 0;
    uint32_t wakeup_attempts    = 0;
    uint32_t wakeup_last_poll   = 0;
    int      suspend_seen       = 0;
    int      wakeup_requested   = 0;
    int      wakeup_ignored     = 0;
    int      resume_seen        = 0;

    VPRINTF(LOW, "MCU: fs_host_remotewakeup_fromdevice test\n");
    boot_mcu();

    // FS boot entry point: sets DEVCMDSTAT FORCE_FULLSPEED to suppress the
    // device-side K-chirp, which is correct only against the FS-only VIP this
    // test configures. It also programs the HUB descriptor RAM and sets HUB_EN.
    boot_usb_core_fs();

    // Not init_interrupts(): that also writes the MCI and I3C interrupt
    // registers, and this early the I3C write does not complete, stalling the
    // LSU pipeline before mstatus.MIE is set.
    intr_count = 0;
    init_usb_interrupts();

    // Second phase of hub bring-up, safe only now that USBDC0's EP list /
    // DEVCMDSTAT / DCON are programmed. Only after HUB_CONNECT does the host
    // see the hub, reset it and enumerate downstream port 0 (USBDC0).
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();

    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request before the host stops SOF.
    // Load-bearing: with FORCE_NEEDCLK still set, utmi_suspendm never falls and
    // there is no suspended state to wake from.
    usb_allow_clock_stop();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);

        // Drain the ISR mailbox: service_usb_intr() already acknowledged
        // INTSTAT, so the foreground loop must not touch it. Snapshot then
        // clear by complement so bits the ISR sets meanwhile are not lost.
        // DSUS/DSUS_C are DEVCMDSTAT bits and do not go through the mailbox.
        usb_events = mcu_intr_rcv.usb;
        mcu_intr_rcv.usb &= ~usb_events;

        // Prefix convention (see libs/usb/usb.h): register ADDRESSES use the
        // device-neutral USB_DEV_* macros, bitfield MASKS use DEV0_CSR_*. The
        // masks are offset-independent within a CSR bank, so they apply to
        // USBDC0 and USBDC1 alike; USB_DEV_SEL parametrizes addresses only.
        if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK)
                usb_handle_control_transfer();
        }
        // EP0 IN completion needs no action: the ISR already acknowledged it.

        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is write-1-to-clear. Read-modify-write the live value
            // rather than reg_data so no other status bit that changed
            // meanwhile is clobbered. The wakeup request below does its own
            // DSUS_C acknowledge.
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

        // Track how long DSUS has read 1 without interruption. Reset on any
        // poll where it is clear, so only a genuinely settled suspend can
        // satisfy the stability requirement below.
        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_MASK)
            dsus_stable_polls++;
        else
            dsus_stable_polls = 0;

        // Arm the wakeup once the controller has been suspended long enough
        // AND DSUS has been stable for several consecutive polls.
        // usb_request_remote_wakeup() re-reads DEVCMDSTAT and refuses if DSUS
        // is no longer set, so a resume that arrives from the host in the
        // meantime cannot turn this into a spurious request.
        if (suspend_seen && !resume_seen && !wakeup_ignored &&
            (wakeup_attempts == 0) &&
            (poll_count - suspend_entry_poll) >= USB_WAKEUP_ARM_DELAY_POLLS &&
            dsus_stable_polls >= USB_WAKEUP_STABLE_DSUS_POLLS) {
            wakeup_attempts++;
            wakeup_last_poll = poll_count;
            if (usb_request_remote_wakeup()) {
                wakeup_requested = 1;
                VPRINTF(LOW, "MCU: remote wakeup driven at poll %d (attempt %d)\n",
                        poll_count, wakeup_attempts);
            } else {
                // Not suspended any more, so there is nothing to wake from.
                // This is not the ignored-command case below and must not be
                // retried: the DUT-side CHK_DEVICE_WAKEUP_K check owns the
                // verdict for a wakeup that never happened.
                wakeup_requested = 1;
                wakeup_ignored   = 1;
                VPRINTF(LOW, "MCU: remote wakeup request refused at poll %d (not suspended)\n",
                        poll_count);
            }
        }

        // Verify the command actually took effect, and re-issue if it did not.
        // usbreg_remotewakeup is a command rather than a latched bit: a write
        // the controller does not act upon leaves no trace, so the only
        // evidence is that DSUS is still set well after the request and no
        // resume followed. Re-issuing is the only available recovery.
        if (wakeup_requested && !resume_seen && !wakeup_ignored &&
            (poll_count - wakeup_last_poll) >= USB_WAKEUP_VERIFY_POLLS) {
            uint32_t cmd_now = lsu_read_32(USB_DEV_DEVCMDSTAT);

            if ((cmd_now & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) == 0u) {
                // Left suspend without DSUS_C being observed above; the
                // resume branch will record it on a later poll.
                wakeup_last_poll = poll_count;
            } else if (wakeup_attempts >= USB_WAKEUP_MAX_ATTEMPTS) {
                wakeup_ignored = 1;
                VPRINTF(LOW,
                    "MCU: ERROR remote wakeup command ignored by controller after %d attempts"
                    " at poll %d (DEVCMDSTAT=0x%x, DSUS still set, no resume K driven)\n",
                    wakeup_attempts, poll_count, cmd_now);
            } else {
                VPRINTF(LOW,
                    "MCU: remote wakeup had no effect after attempt %d (DEVCMDSTAT=0x%x);"
                    " re-issuing at poll %d\n",
                    wakeup_attempts, cmd_now, poll_count);
                wakeup_attempts++;
                wakeup_last_poll = poll_count;
                (void)usb_request_remote_wakeup();
            }
        }

        // Observation complete. Keep serving EP0 for a bounded grace window so
        // the sequence's post-resume control transfer can finish, then stop.
        // The simulation cannot end early: the test holds a run_phase objection
        // until csr_write_mpmc_halt() is reached below. Spinning on to
        // USB_POLL_TIMEOUT would only add wall-clock time.
        if ((resume_seen && wakeup_requested) || wakeup_ignored) {
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
        VPRINTF(LOW, "MCU: suspend at poll %d, resume at poll %d (wakeup attempts %d)\n",
                suspend_entry_poll, resume_poll, wakeup_attempts);

    // Firmware verdict byte. Only the FAIL code is ever sent: TB_CMD_TEST_PASS
    // makes the testbench $finish immediately, which would pre-empt the UVM
    // final_phase where CHK_DEVICE_WAKEUP_K and the UVM error counts are
    // judged. Report the firmware-visible failures explicitly so a dropped
    // wakeup command is attributable here, at the register, instead of only
    // surfacing as a missing K in the checker several hundred microseconds
    // later.
    if (!suspend_seen || !wakeup_requested || !resume_seen || wakeup_ignored) {
        VPRINTF(LOW, "MCU: fs_host_remotewakeup_fromdevice - reporting FAIL to testbench\n");
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    VPRINTF(LOW, "MCU: fs_host_remotewakeup_fromdevice test complete\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
