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
// Description: USB FS "token to an unsupported endpoint" test firmware for the
//              Caliptra SS.
//
// The host VIP sends a BULK OUT token to an endpoint number that has no
// physical endpoint behind it at all. USB_C_DEV0_NBPHYSEP / USB_C_DEV1_NBPHYSEP
// are 28 (see src/integration/rtl/caliptra_ss_top.sv), i.e. 14 OUT/IN pairs, so
// endpoint numbers 1..14 are backed by a descriptor slot and endpoint 15 is the
// first one that is not. The device must ignore such a token completely: no
// ACK, no NAK, no STALL.
//
// This firmware is deliberately minimal. There is no descriptor slot to program
// and nothing to watch on the device side, so it only:
//   - Boots the MCU and the USB core in FS device mode behind the on-chip hub
//     (boot_usb_core_fs(), which keeps the device from chirping so the link
//     settles at Full Speed)
//   - Services enumeration (bus reset + EP0 SETUP packets) so the host can
//     address the device
// The verdict for the unsupported-endpoint probe itself is made on the host
// side by the handshake counter in the UVM sequence.
//
// Verdict: FAIL-only. total_errors is never reset; any detected problem
// increments it and the run is failed once at the end with TB_CMD_TEST_FAIL.
// TB_CMD_TEST_PASS is never sent.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Full Speed is roughly 40x slower on the wire than High Speed, so the MCU
// event loop needs a much higher poll ceiling than the HS sibling (30000) to
// stay alive through enumeration plus the host-side silence window. Same
// value as the other FS device tests (see caliptra_ss_usb_fs_dev_bulk_out.c).
#define USB_POLL_TIMEOUT 21000

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Never reset. Incremented on every detected problem; drives the single
// TB_CMD_TEST_FAIL at the end of main().
static uint32_t total_errors = 0;

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;

    VPRINTF(LOW, "=================\nMCU: USB FS unsupported-endpoint test\n=================\n\n");

    boot_mcu();
    // FS variant: boot_usb_core_fs() programs the device to suppress the HS
    // chirp so the host keeps the link at Full Speed. It also runs
    // usb_hub_init_and_connect() internally, so only HUB_CONNECT is left.
    boot_usb_core_fs();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
            }
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_DEV_INT_MASK);
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                // SETUP packet received - decode and respond.
                usb_handle_control_transfer();
            } else {
                // Status-stage ZLP OUT for a control read completed. Hardware
                // cleared ACTIVE on the EP0 OUT descriptor, so re-arm it or the
                // next SETUP is NAK'd and enumeration stalls.
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        if (poll_count % 2000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT));
        }
    }

    if (total_errors != 0) {
        VPRINTF(LOW, "MCU: USB FS unsupported-endpoint test - %d error(s)\n", total_errors);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    } else {
        VPRINTF(LOW, "MCU: USB FS unsupported-endpoint test - all firmware checks passed\n");
    }

    VPRINTF(LOW, "MCU: USB FS unsupported-endpoint test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
