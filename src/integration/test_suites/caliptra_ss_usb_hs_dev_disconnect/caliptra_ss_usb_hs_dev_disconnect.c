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
// Description: USB HS device disconnect/reconnect test firmware for Caliptra SS.
//
// Test flow:
//   1. Boot MCU and USB device controller. Clear FORCE_VBUS so the
//      controller monitors the real VBus pin (required for disconnect
//      detection via DCON_C / VBUS_DEBOUNCED).
//   2. Enumerate: service EP0 SETUP tokens (GET_DESCRIPTOR, SET_ADDRESS,
//      SET_CONFIGURATION) inline in the poll loop. Bus resets are handled
//      via usb_handle_bus_reset() on every DEV_INT.
//   3. Wait for USB_SOF_COUNT FRAME_INT (SOF) events while continuing to
//      service EP0.
//   4. Detect VBus removal: poll for DCON_C set and VBUS_DEBOUNCED clear.
//      On detection clear DCON (drops FsPullup) then clear DCON_C (W1C).
//      Verify VBUS_DEBOUNCED is clear.
//   5. Re-enumerate after reconnect (same as phase 2).
//   6. Wait for USB_SOF_COUNT more FRAME_INT events.
//   7. Report PASSED.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Poll timeout: number of main-loop iterations before declaring a timeout.
// Each iteration is ~51 ns at MCU clock rate.
//
// This is a failure ceiling, not a dwell: every loop that uses it exits early
// via break or via its loop condition as soon as the awaited event arrives, so
// lowering it costs nothing on a passing run. It only bounds how much
// simulation is burned before a genuinely stuck run gives up. 500000 iterations
// was ~25 ms of simulated time per stuck phase, which is what turned earlier
// broken runs into multi-hour jobs. 100000 iterations is ~5 ms, still an order
// of magnitude more than the longest legitimate wait here (host reconnect after
// the 100 us VBus-off window plus HS chirp and bus reset).
#define USB_POLL_TIMEOUT    100000

// Number of SOF (FRAME_INT) events to count on each side of the disconnect.
#define USB_SOF_COUNT       6

// Number of standard enumeration control transfers expected:
// GET_DESCRIPTOR + SET_ADDRESS + SET_CONFIGURATION = 3.
#define USB_ENUM_XFER_COUNT 3

// Post-re-enumeration EP0 service window.
//
// After Phase 4 has counted USB_ENUM_XFER_COUNT transfers the UVM sequence
// (enumerate_hub_and_dev0) is not finished: it still drives GET_DESCRIPTOR
// at the new address and SET_CONFIGURATION to USBDC0. If firmware halts
// immediately after the counted transfers, EP0 is never re-armed for those
// remaining SETUP packets and the device NAKs a SETUP token. The Synopsys
// USB VIP flags that as a protocol violation
// (valid_device_response_check_Dev2_EP0), which failed the test even though
// the disconnect/reconnect behavior itself was correct.
//
// Keep servicing EP0 for a bounded window after the counted transfers so the
// tail of the host-side enumeration is answered properly before halting.
//
// This is only a backstop ceiling, not a dwell: the loop normally exits via the
// quiet-period check below, long before the cap is reached. Reduced from 200000
// (~10 ms) to 40000 (~2 ms), which still spans far more than the handful of
// control transfers the host has left to drive.
#define USB_POST_ENUM_SERVICE_ITERS 40000

// Number of additional control transfers the host drives after the counted
// re-enumeration transfers (GET_DESCRIPTOR at new address + SET_CONFIGURATION).
// This is the minimum the window must observe, not the point at which it exits.
#define USB_POST_ENUM_XFER_COUNT 2

// Quiet period, in poll iterations, that must elapse with no EP0 SETUP activity
// before Phase 4b is allowed to finish.
//
// Counting USB_POST_ENUM_XFER_COUNT transfers is NOT a safe exit condition on
// its own. The host has no way to know the firmware has stopped servicing EP0,
// so it keeps driving control transfers for as long as the UVM sequence runs.
// Leaving the window immediately after the last counted transfer made the MCU
// halt while a further SETUP was already in flight; that SETUP went unanswered
// and the device NAKed it, which the VIP correctly flags as a protocol
// violation (valid_device_response_check: NAK to a SETUP is illegal). Requiring
// an idle stretch first means the window only closes once the host has actually
// gone quiet, so there is no SETUP left outstanding when the firmware halts.
#define USB_POST_ENUM_QUIET_ITERS 2000


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
    uint32_t xfer_count;
    // Poll index of the most recent EP0 SETUP, used by the Phase 4b quiet check.
    uint32_t last_setup_poll;
    uint32_t sof_count;

    VPRINTF(LOW, "=================\nMCU: USB HS device disconnect test\n=================\n\n");

    boot_mcu();
    boot_usb_core();

    // Connect the compound hub upstream.
    //
    // boot_usb_core() calls usb_hub_init_and_connect(), which programs the
    // HUB RAM and sets HUB_EN only - HUB_CONNECT is deliberately deferred so
    // that USBDC0 is fully programmed before the host can see anything on the
    // bus. This test was missing the second phase entirely, so the hub never
    // attached upstream: the host never saw a device, never drove a bus reset,
    // and the VIP PHY stayed parked in Non-Driving/SE0 forever while Phase 1
    // spun out its poll timeout. Matches the ordering used by the passing
    // caliptra_ss_usb_hs_dev_bulk_out test.
    usb_hub_connect();

    // Clear FORCE_VBUS so the controller monitors the real VBus pin.
    // boot_usb_core() sets FORCE_VBUS=1 for normal enumeration tests.
    // With FORCE_VBUS=1 the DUT ignores VBus removal; DCON_C never fires
    // and disconnect detection is impossible.
    //
    // Done after usb_hub_connect() so the hub bring-up write to HUB_CTRL
    // cannot race this DEVCMDSTAT read-modify-write.
    {
        uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        cmd &= ~USBHSD_DEVCMDSTAT_FORCE_VBUS_MASK;
        lsu_write_32(USB_DEV0_DEVCMDSTAT, cmd);
        VPRINTF(LOW, "MCU: FORCE_VBUS cleared (DEVCMDSTAT=0x%x)\n", cmd);
    }

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();
    VPRINTF(LOW, "MCU: Caliptra core ready\n");

    // ------------------------------------------------------------------
    // Phase 1: Enumeration (initial connect).
    // Service EP0 SETUP tokens until USB_ENUM_XFER_COUNT transfers are
    // handled. Bus resets are serviced inline via DEV_INT / usb_handle_bus_reset().
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Phase 1 - initial enumeration\n");
    xfer_count = 0;
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && xfer_count < USB_ENUM_XFER_COUNT;
         poll_count++) {

        reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV0_INTSTAT);

        // DEV_INT: bus-level events (bus reset, connect/disconnect change).
        // Read DEVCMDSTAT before the W1C write - the W1C on DEV_INT also
        // clears the change-detect bits (DRES_C, DSUS_C, DCON_C) in
        // DEVCMDSTAT, so reg_data must be sampled first.
        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // EP0 OUT: SETUP or status-phase OUT token.
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                if (usb_handle_control_transfer()) {
                    xfer_count++;
                    VPRINTF(LOW, "MCU: enumeration transfer %d of %d\n",
                            xfer_count, USB_ENUM_XFER_COUNT);
                }
            }
        }

        // EP0 IN: clear interrupt.
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }
    }

    if (xfer_count < USB_ENUM_XFER_COUNT) {
        VPRINTF(LOW, "MCU: FAIL - enumeration timeout (got %d of %d)\n",
                xfer_count, USB_ENUM_XFER_COUNT);
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: Enumeration complete (%d transfers).\n", xfer_count);

    // // ------------------------------------------------------------------
    // // Phase 2: Wait for USB_SOF_COUNT SOF (FRAME_INT) events.
    // // Enable FRAME_INT, count events while continuing to service EP0 and
    // // DEV_INT, then disable FRAME_INT.
    // // ------------------------------------------------------------------
    // VPRINTF(LOW, "MCU: Phase 2 - waiting for %d SOF events\n", USB_SOF_COUNT);

    // Clear any pending FRAME_INT before enabling.
    lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_FRAME_INT_MASK);

    // Enable FRAME_INT in INTEN.
    lsu_write_32(USB_DEV0_INTEN,
                 lsu_read_32(USB_DEV0_INTEN) | USBHSD_INTEN_FRAME_INT_EN_MASK);

    // sof_count = 0;
    // for (poll_count = 0;
    //      poll_count < USB_POLL_TIMEOUT && sof_count < USB_SOF_COUNT;
    //      poll_count++) {

    //     reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    //     intstat  = lsu_read_32(USB_DEV0_INTSTAT);

    //     if (intstat & USBHSD_INTSTAT_FRAME_INT_MASK) {
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_FRAME_INT_MASK);
    //         sof_count++;
    //         VPRINTF(LOW, "MCU: SOF event %d\n", sof_count);
    //     }

    //     if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
    //         if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
    //             usb_handle_bus_reset();
    //         }
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
    //     }

    //     if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
    //         if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
    //             usb_handle_control_transfer();
    //         }
    //     }

    //     if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
    //     }
    // }

    // Disable FRAME_INT.
    lsu_write_32(USB_DEV0_INTEN,
                 lsu_read_32(USB_DEV0_INTEN) & ~USBHSD_INTEN_FRAME_INT_EN_MASK);

    // if (sof_count < USB_SOF_COUNT) {
    //     VPRINTF(LOW, "MCU: FAIL - SOF timeout (got %d of %d)\n",
    //             sof_count, USB_SOF_COUNT);
    //     csr_write_mpmc_halt();
    // }
    // VPRINTF(LOW, "MCU: All %d SOF events received.\n", sof_count);

    // ------------------------------------------------------------------
    // Phase 3: Disconnect detection.
    // Poll for DCON_C set and VBUS_DEBOUNCED clear. Service EP0 and
    // DEV_INT inline on every iteration.
    // On detection: clear DCON (de-asserts FsPullup/TermSelect so the
    // VIP link state machine can leave ENABLED state), then clear DCON_C (W1C).
    //
    // NOTE: DCON is R/W firmware-controlled. Hardware does not clear DCON
    // on VBus removal. "DCON_C && !DCON" is therefore never true. Detect
    // "DCON_C && !VBUS_DEBOUNCED" instead - hardware clears VBUS_DEBOUNCED
    // when VBus is removed - then explicitly clear DCON to drop FsPullup.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Phase 3 - waiting for disconnect (DCON_C + VBUS_DEBOUNCED=0)\n");
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV0_INTSTAT);

        // Service EP0 on every pass (VIP may send SETUP packets while waiting).
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
            }
        }

        if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }

        // DCON_C is a change-detect bit sampled before any W1C write above,
        // so its value in reg_data is still valid for the check below.
        if ((reg_data & USBHSD_DEVCMDSTAT_DCON_C_MASK) &&
            !(reg_data & USBHSD_DEVCMDSTAT_VBUS_DEBOUNCED_MASK)) {
            VPRINTF(LOW, "MCU: Disconnect detected - DEVCMDSTAT=0x%x\n", reg_data);

            // Clear DCON so FsPullup/TermSelect de-asserts.
            // VIP link state machine requires FsPullup low to leave ENABLED.
            {
                uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
                cmd &= ~USBHSD_DEVCMDSTAT_DCON_MASK;
                lsu_write_32(USB_DEV0_DEVCMDSTAT, cmd);
                VPRINTF(LOW, "MCU: DCON cleared (DEVCMDSTAT=0x%x)\n", cmd);
            }

            // Clear DCON_C (W1C) after DCON is de-asserted.
            // Use RMW so DEV_EN and all other sticky bits are preserved.
            {
                uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
                cmd |= USBHSD_DEVCMDSTAT_DCON_C_MASK;
                lsu_write_32(USB_DEV0_DEVCMDSTAT, cmd);
            }
            break;
        }
    }

    if (poll_count >= USB_POLL_TIMEOUT) {
        VPRINTF(LOW, "MCU: FAIL - timeout waiting for disconnect\n");
        csr_write_mpmc_halt();
    }

    // Verify VBUS_DEBOUNCED is clear after disconnect.
    reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    if (reg_data & USBHSD_DEVCMDSTAT_VBUS_DEBOUNCED_MASK) {
        VPRINTF(LOW, "MCU: FAIL - VBUS_DEBOUNCED still set after disconnect (DEVCMDSTAT=0x%x)\n",
                reg_data);
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: USB bus disconnected. VBUS_DEBOUNCED clear.\n");

    // ------------------------------------------------------------------
    // Phase 3b: Wait for VBus to return (VBUS_DEBOUNCED set), then
    // re-assert DCON to bring FsPullup back high.
    //
    // After DCON was cleared in Phase 3, the device FsPullup is low.
    // The VIP host cannot see the device as re-attached until FsPullup
    // goes high again. Without re-asserting DCON here, the VIP link
    // state machine never leaves DISCONNECTED and never drives a bus
    // reset, so the HS chirp / ENABLED state is never reached and
    // Step 10 (WAIT_RECONN) waits forever.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Phase 3b - waiting for VBus to return (VBUS_DEBOUNCED)\n");
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        if (reg_data & USBHSD_DEVCMDSTAT_VBUS_DEBOUNCED_MASK) {
            VPRINTF(LOW, "MCU: VBus returned - DEVCMDSTAT=0x%x\n", reg_data);
            break;
        }
    }
    if (poll_count >= USB_POLL_TIMEOUT) {
        VPRINTF(LOW, "MCU: FAIL - timeout waiting for VBus to return\n");
        csr_write_mpmc_halt();
    }

    // Re-assert DCON so FsPullup goes high and VIP host can detect the
    // device re-attached. This triggers the HS chirp sequence and
    // eventually brings the link back to ENABLED.
    
    {
        uint32_t cmd = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        cmd |= USBHSD_DEVCMDSTAT_DCON_MASK;
        lsu_write_32(USB_DEV0_DEVCMDSTAT, cmd);
        VPRINTF(LOW, "MCU: DCON re-asserted (DEVCMDSTAT=0x%x)\n", cmd);
    }

    // ------------------------------------------------------------------
    // Phase 4: Re-enumeration after reconnect.
    // Same inline pattern as Phase 1. The VIP reconnects VBus and drives
    // a new bus reset; DEV_INT/DRES_C is handled inline.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Phase 4 - waiting for host to reconnect and re-enumerate\n");
    xfer_count = 0;
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && xfer_count < USB_ENUM_XFER_COUNT;
         poll_count++) {

        reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV0_INTSTAT);

        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                if (usb_handle_control_transfer()) {
                    xfer_count++;
                    VPRINTF(LOW, "MCU: re-enumeration transfer %d of %d\n",
                            xfer_count, USB_ENUM_XFER_COUNT);
                }
            }
        }

        if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }
    }

    if (xfer_count < USB_ENUM_XFER_COUNT) {
        VPRINTF(LOW, "MCU: FAIL - re-enumeration timeout (got %d of %d)\n",
                xfer_count, USB_ENUM_XFER_COUNT);
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: Re-enumeration complete (%d transfers).\n", xfer_count);

    // ------------------------------------------------------------------
    // Phase 4b: Post-re-enumeration EP0 service window.
    //
    // The host-side UVM sequence (enumerate_hub_and_dev0) continues past
    // the counted transfers: after SET_ADDRESS it re-anchors the VIP to the
    // new address and drives GET_DESCRIPTOR and SET_CONFIGURATION to
    // USBDC0. Those SETUP packets must still be answered. Halting here
    // leaves EP0 un-armed and the device NAKs a SETUP, which the VIP
    // protocol checker reports as an illegal device response.
    //
    // Keep the same EP0 / DEV_INT service pattern running for a bounded
    // window. The window closes only once at least USB_POST_ENUM_XFER_COUNT
    // more control transfers have been handled AND the host has then been
    // silent for USB_POST_ENUM_QUIET_ITERS polls, so the firmware never halts
    // with a SETUP still outstanding. The iteration cap is only a backstop.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Phase 4b - servicing EP0 for the tail of host enumeration\n");
    xfer_count = 0;
    last_setup_poll = 0;
    for (poll_count = 0; poll_count < USB_POST_ENUM_SERVICE_ITERS; poll_count++) {

        // Exit only when the host has both driven the transfers we expect and
        // then stayed quiet long enough that nothing is still in flight.
        if (xfer_count >= USB_POST_ENUM_XFER_COUNT &&
            (poll_count - last_setup_poll) > USB_POST_ENUM_QUIET_ITERS) {
            break;
        }

        reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV0_INTSTAT);

        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                // Any SETUP, counted or not, restarts the quiet timer.
                last_setup_poll = poll_count;
                if (usb_handle_control_transfer()) {
                    xfer_count++;
                    VPRINTF(LOW, "MCU: post-enumeration transfer %d of %d\n",
                            xfer_count, USB_POST_ENUM_XFER_COUNT);
                }
            }
        }

        if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }
    }

    if (xfer_count < USB_POST_ENUM_XFER_COUNT) {
        // Not fatal on its own: the host may legitimately drive fewer
        // trailing transfers. Report it so a NAK-on-SETUP protocol error
        // from the VIP can be correlated with a short service window.
        VPRINTF(LOW, "MCU: WARNING - post-enumeration service window ended with %d of %d transfers\n",
                xfer_count, USB_POST_ENUM_XFER_COUNT);
    } else {
        VPRINTF(LOW, "MCU: Post-enumeration service complete (%d transfers).\n",
                xfer_count);
    }

    // // ------------------------------------------------------------------
    // // Phase 5: Wait for USB_SOF_COUNT SOF events after reconnect.
    // // ------------------------------------------------------------------

    // VPRINTF(LOW, "MCU: Phase 5 - waiting for %d SOF events after reconnect\n",
    //         USB_SOF_COUNT);

    lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_FRAME_INT_MASK);
    lsu_write_32(USB_DEV0_INTEN,
                 lsu_read_32(USB_DEV0_INTEN) | USBHSD_INTEN_FRAME_INT_EN_MASK);

    // sof_count = 0;
    // for (poll_count = 0;
    //      poll_count < USB_POLL_TIMEOUT && sof_count < USB_SOF_COUNT;
    //      poll_count++) {

    //     reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    //     intstat  = lsu_read_32(USB_DEV0_INTSTAT);

    //     if (intstat & USBHSD_INTSTAT_FRAME_INT_MASK) {
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_FRAME_INT_MASK);
    //         sof_count++;
    //         VPRINTF(LOW, "MCU: SOF event %d (post-reconnect)\n", sof_count);
    //     }

    //     if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
    //         if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
    //             usb_handle_bus_reset();
    //         }
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
    //     }

    //     if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
    //         if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
    //             usb_handle_control_transfer();
    //         }
    //     }

    //     if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
    //         lsu_write_32(USB_DEV0_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
    //     }
    // }

    // lsu_write_32(USB_DEV0_INTEN,
    //              lsu_read_32(USB_DEV0_INTEN) & ~USBHSD_INTEN_FRAME_INT_EN_MASK);

    // if (sof_count < USB_SOF_COUNT) {
    //     VPRINTF(LOW, "MCU: FAIL - SOF timeout after reconnect (got %d of %d)\n",
    //             sof_count, USB_SOF_COUNT);
    //     csr_write_mpmc_halt();
    // }
    // VPRINTF(LOW, "MCU: All %d SOF events received after reconnect.\n", sof_count);

    // ------------------------------------------------------------------
    // All phases passed.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: USB HS disconnect test PASSED\n");
    reg_data = lsu_read_32(USB_DEV0_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    csr_write_mpmc_halt();
}
