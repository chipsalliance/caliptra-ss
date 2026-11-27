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

// Description: MCU firmware for the hub downstream PORT_SUSPEND + REMOTE WAKEUP
// test (HIGH SPEED). Coverage target: the hub_port_remotewakeup branch of
// PROC_REQUEST_HANDLING in usb_app_hw_hub.m.vhdl, whose inner condition needs
// hub_port_suspend_int(i) = 1 at the moment the device raises remote wakeup.
//
// The upstream bus is NOT suspended: SOF keeps running and the hub stays active.
// The host suspends only the downstream port with SetPortFeature(PORT_SUSPEND).
// That makes the hub assert the per-port suspend toward USBDC0, which reports
// DEVCMDSTAT.DSUS = 1. This firmware then requests a remote wakeup by itself
// once DSUS has been stable for USB_WAKEUP_STABLE_DSUS_POLLS polls, using the
// normal usb_request_remote_wakeup() helper. No host-to-MCU command is needed,
// so no new MCU opcode is introduced.
//
// The wake is timed in polls on the MCU side. The host sequence does not depend
// on that timing: it polls GetPortStatus until the port suspend bit drops, with
// a bounded number of attempts.
//
// The pass/fail verdict lives in the UVM sequence (port status ladder and a
// post-wake GetDescriptor). The checks here are log only.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Safety ceiling on the polling loop. The normal exit is host driven, see
// USB_POSTRESUME_DESC_COUNT below.
#define USB_POLL_TIMEOUT 50000

// Second GetDescriptor(Device) read at the assigned address is the post-wake
// traffic check of the sequence (the first one closes enumeration).
#define USB_POSTRESUME_DESC_COUNT 2

// Polls served after the post-wake descriptor read before halting.
#define USB_POST_CHECK_GRACE_POLLS 500

// Consecutive polls DSUS must read 1 before the wakeup is requested. About
// 1500 polls is well above the host's PORT_SUSPEND status read and well below
// the end of the host's observation window.
#define USB_WAKEUP_STABLE_DSUS_POLLS 1500

// usbreg_remotewakeup is a command, not a latched bit. If DSUS is still set
// this many polls after a request, the request is repeated.
#define USB_WAKEUP_VERIFY_POLLS 2000
#define USB_WAKEUP_MAX_ATTEMPTS 3

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

    uint32_t dsus_stable_polls = 0;
    uint32_t wakeup_attempts   = 0;
    uint32_t wakeup_last_poll  = 0;
    int      suspend_seen      = 0;
    int      resume_seen       = 0;

    bool     addr_assigned  = false;
    uint32_t dev_desc_reads = 0;
    bool     check_done     = false;
    uint32_t grace_polls    = 0;

    VPRINTF(LOW, "MCU: hs_dev_hub_port_suspend_remotewake test\n");
    boot_mcu();

    // Bring up USBDC0 behind the on-chip hub (HUB_EN is set inside), then
    // connect the hub upstream so the host can enumerate it.
    boot_usb_core_hub();
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request, as the other suspend tests.
    usb_allow_clock_stop();

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        usb_handle_bus_reset();
        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);

        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();

                // Classified after the handler returns so EP0 is armed first.
                usb_setup_pkt_t pkt = usb_last_setup;

                if (USB_BMREQTYPE_TYPE(pkt.bmRequestType) == USB_TYPE_STANDARD &&
                    USB_BMREQTYPE_RECIPIENT(pkt.bmRequestType) == USB_RECIP_DEVICE) {
                    if (pkt.bRequest == USB_REQ_SET_ADDRESS &&
                        (pkt.wValue & 0x7Fu) != 0u) {
                        addr_assigned = true;
                    }
                    else if (pkt.bRequest == USB_REQ_GET_DESCRIPTOR &&
                             ((pkt.wValue >> 8) & 0xFFu) == USB_DESC_DEVICE &&
                             addr_assigned) {
                        dev_desc_reads++;
                        if (!check_done &&
                            dev_desc_reads >= USB_POSTRESUME_DESC_COUNT) {
                            check_done = true;
                            VPRINTF(LOW, "MCU: post-wake GetDescriptor(Device) served (read %d) after %d polls; halting shortly\n",
                                    dev_desc_reads, poll_count + 1);
                        }
                    }
                }
            }
        }
        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);

        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK) {
            // DSUS_C is write-1-to-clear. The live value is written back with
            // bit 17 (DSUS) as read, so this write never requests a wakeup.
            lsu_write_32(USB_DEV_DEVCMDSTAT,
                lsu_read_32(USB_DEV_DEVCMDSTAT) | DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) {
                if (!suspend_seen) {
                    suspend_seen = 1;
                    VPRINTF(LOW, "MCU: port suspend reported by DSUS at poll %d DEVCMDSTAT=0x%x\n",
                            poll_count, reg_data);
                }
            } else if (suspend_seen && !resume_seen) {
                resume_seen = 1;
                VPRINTF(LOW, "MCU: DSUS dropped (remote wakeup took effect) at poll %d DEVCMDSTAT=0x%x\n",
                        poll_count, reg_data);
            }
        }

        if (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_MASK)
            dsus_stable_polls++;
        else
            dsus_stable_polls = 0;

        // Request the remote wakeup. usb_request_remote_wakeup() re-reads
        // DEVCMDSTAT and refuses when DSUS is no longer set.
        if (suspend_seen && !resume_seen && wakeup_attempts == 0 &&
            dsus_stable_polls >= USB_WAKEUP_STABLE_DSUS_POLLS) {
            wakeup_attempts++;
            wakeup_last_poll = poll_count;
            if (usb_request_remote_wakeup())
                VPRINTF(LOW, "MCU: remote wakeup driven at poll %d (attempt %d)\n",
                        poll_count, wakeup_attempts);
            else
                VPRINTF(LOW, "MCU: remote wakeup refused at poll %d (not suspended)\n",
                        poll_count);
        }
        else if (wakeup_attempts > 0 && wakeup_attempts < USB_WAKEUP_MAX_ATTEMPTS &&
                 !resume_seen && (reg_data & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) &&
                 (poll_count - wakeup_last_poll) >= USB_WAKEUP_VERIFY_POLLS) {
            wakeup_attempts++;
            wakeup_last_poll = poll_count;
            VPRINTF(LOW, "MCU: DSUS still set, repeating remote wakeup (attempt %d)\n",
                    wakeup_attempts);
            (void)usb_request_remote_wakeup();
        }

        if (check_done) {
            if (grace_polls >= USB_POST_CHECK_GRACE_POLLS) {
                VPRINTF(LOW, "MCU: grace window of %d polls served; ending poll loop at poll %d\n",
                        USB_POST_CHECK_GRACE_POLLS, poll_count + 1);
                break;
            }
            grace_polls++;
        }
    }

    if (!suspend_seen)
        VPRINTF(LOW, "MCU: WARNING DSUS never reported the port suspend, so no remote wakeup was requested; see the UVM sequence log.\n");
    if (!check_done)
        VPRINTF(LOW, "MCU: WARNING poll ceiling of %d reached without serving the post-wake GetDescriptor(Device) (reads=%d, address assigned=%d).\n",
                USB_POLL_TIMEOUT, dev_desc_reads, (int)addr_assigned);

    VPRINTF(LOW, "MCU: hs_dev_hub_port_suspend_remotewake test complete\n");
    csr_write_mpmc_halt();
}
