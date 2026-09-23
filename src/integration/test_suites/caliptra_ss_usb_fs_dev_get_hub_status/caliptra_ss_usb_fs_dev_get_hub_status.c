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
// Description: USB Full-Speed GetHubStatus test firmware for the Caliptra SS.
//
//
//
// This firmware:
//   - Boots the MCU and USB core in HS device mode via boot_usb_core_fs()
//   - Connects the on-chip hub upstream (two-phase HUB_EN then HUB_CONNECT)
//   - Polls DEVCMDSTAT directly for SETUP packets and services EP0 control
//     transfers via the shared usb.c dispatcher (no interrupt machinery)
//
// The protocol exercised by this test (SetFeature/ClearFeature(DEVICE_REMOTE_
// WAKEUP) + GET_STATUS for the hub and dev0) is handled inside the shared
// usb.c control-transfer dispatcher: usb_handle_control_transfer() honors
// SET_FEATURE(DEVICE_REMOTE_WAKEUP) by setting a shadow flag and CLEAR_FEATURE
// by clearing it, and a subsequent GET_STATUS returns 0x0002 (bit1 =
// Remote-Wakeup) or 0x0000 accordingly. No test-specific firmware logic is
// needed here beyond the standard poll loop.
//
// Structured to mirror caliptra_ss_usb_fs_conn.c: this is a pure polling test
// with no ISR involvement (no mcu_isr.h, no init_usb_interrupts(), no ISR
// mailbox). SETUP packets are detected by reading DEVCMDSTAT.SETUP directly.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT 20000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t reg_data;
    uint32_t intstat;
    uint32_t poll_count;
    uint32_t transfers_handled = 0;

    VPRINTF(LOW, "=================\nMCU: USB get_hub_status test\n=================\n\n");

    boot_mcu();

    // boot_usb_core_fs() brings up the USB device controller in HS mode. On the
    // new hub-composite IP it also programs+validates the HUB RAM and sets
    // HUB_EN (via usb_hub_init_and_connect()); USBDC0 is an embedded downstream
    // device of the on-chip hub, not a device directly on the bus.
    // FS-only bring-up: boot_usb_core_fs() sets DEVCMDSTAT.PFSC (bit 21) to
    // suppress the device-side K-chirp so the link negotiates and stays at
    // full speed for the FS-only host VIP (high_speed_capable=0).
    boot_usb_core_fs();

    // Two-phase hub bring-up: HUB_EN was set inside boot_usb_core_fs(); now that
    // USBDC0's EP list / DEVCMDSTAT / DCON are fully programmed it is safe to
    // connect the hub upstream. usb_hub_connect() sets HUB_CONNECT, per the
    // reference janus_hub_ctrl_bfm.sv two-phase sequencing. Only after this
    // will the host see the hub on the bus and enumerate its downstream port 0
    // (USBDC0).
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();

    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    // Read initial USB state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INTSTAT);
    VPRINTF(LOW, "MCU: USB INTSTAT = 0x%x\n", reg_data);

    // --- Main USB event loop: poll INTSTAT for USB events ---
    //
    // Canonical Category-B pure-polling loop (see
    // claude_md/17_usb_polling_intstat_clearing.md): read INTSTAT each
    // iteration and write-1-to-clear each serviced bit (DEV_INT, EP0OUT,
    // EP0IN). boot_usb_core_fs() enables DEV_INT|EP0OUT|EP0IN in INTEN, and
    // usb.c only clears EP0IN, so gating solely on DEVCMDSTAT.SETUP (the old
    // loop) left EP0OUT/DEV_INT permanently asserting dev0_usb_irq.
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        // Direct DEVCMDSTAT poll for bus reset (fallback path; DEV_INT is
        // also cleared below when observed in INTSTAT).
        usb_handle_bus_reset();

        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);

        // Device-level interrupt (bus reset / connect change). W1C DEV_INT.
        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // EP0 OUT interrupt (SETUP or status-stage OUT). W1C EP0OUT first,
        // then service the SETUP packet if DEVCMDSTAT.SETUP is set. Do not
        // VPRINTF before usb_handle_control_transfer(): each VPRINTF adds
        // ~1-2us and the host VIP gives up on IN polling ~5us after the
        // SETUP ACK. Logging happens inside the handler after the SETUP bit
        // is cleared.
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                transfers_handled++;
            } else {
                // Status-stage ZLP OUT completed (no SETUP). HW cleared the
                // EP0 OUT ACTIVE bit; re-arm it so the next SETUP is received
                // rather than NAKed.
                usb_ep0_arm_out();
            }
        }

        // EP0 IN interrupt (control-read data / status stage). W1C EP0IN.
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);
        }

        // Periodic diagnostic dump
        if (poll_count % 1000 == 0 && poll_count > 0) {
            uint32_t diag_cmd     = lsu_read_32(USB_DEV_DEVCMDSTAT);
            uint32_t diag_int     = lsu_read_32(USB_DEV_INTSTAT);
            uint32_t ep0_out      = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x000);
            uint32_t ep0_in_diag  = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP_LIST_OFFSET + 0x008);

            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x EP0OUT=0x%x EP0IN=0x%x transfers=%d\n",
                    poll_count, diag_cmd, diag_int, ep0_out, ep0_in_diag, transfers_handled);
        }
    }

    // Report final state
    reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: USB DEVCMDSTAT final = 0x%x\n", reg_data);
    reg_data = lsu_read_32(USB_DEV_INFO);
    VPRINTF(LOW, "MCU: USB INFO final = 0x%x\n", reg_data);

    VPRINTF(LOW, "MCU: USB get_hub_status test - transfers handled: %d\n", transfers_handled);

    VPRINTF(LOW, "MCU: USB get_hub_status test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
