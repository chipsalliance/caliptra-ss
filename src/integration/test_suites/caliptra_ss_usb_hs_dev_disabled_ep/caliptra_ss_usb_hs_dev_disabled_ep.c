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
// Description: USB HS "token to a DISABLED endpoint" test firmware for the
//              Caliptra SS.
//
// Scenario. The firmware marks endpoint 4 OUT as DISABLED in the endpoint
// command/status list, and the host VIP then sends one short BULK OUT to that
// endpoint. The device must ignore the transaction completely: no ACK, no NAK,
// no STALL. The verdict for the silence itself is made on the host side by the
// handshake counter in the UVM sequence; this firmware owns the device-side
// setup and the device-side checks.
//
// WHY THE DESCRIPTOR AND NOT A REGISTER. Enabling or disabling an endpoint on
// this controller is NOT a control-register operation. The three endpoint CSRs
// are buffer controls, not enables:
//   EPSKIP   (0x14) one-shot, self-clearing abort of the endpoint's current
//                   buffer. Firmware writes a 1 and the hardware clears it
//                   again once the DMA has deactivated the buffer
//                   (usb_reg_if.m.vhdl:689 firmware write,
//                   usb_reg_if.m.vhdl:782 hardware clear). It is not a
//                   persistent enable.
//   EPINUSE  (0x18) double-buffering: which of buffer 0/1 the hardware uses.
//   EPBUFCFG (0x1c) single versus double buffering per endpoint.
// The only enable in the register interface is the whole-device DEV_EN
// (usb_reg_if.m.vhdl:187 usbreg_deviceenabled <= reg_dev_enable).
//
// The per-endpoint enable lives in the endpoint command/status list word in
// system memory, as bit 30, the D (Disabled) field:
//   "D (Disabled) RW - 0: EP enabled, 1: EP disabled. On bus reset, FW should
//    disable all EPs. FW can modify only when Active is 0."
// The hardware path is:
//   usb_dma.m.vhdl:300   epinfo_disabled <= dma_rdata(30)
//                        (forced to '0' when the endpoint number is 0, so the
//                         D field has no effect on EP0)
//   usb_pie.m.vhdl:2482  OUT path, and
//   usb_pie.m.vhdl:2366  IN / PING path:
//                        "ep is disabled. no data nor handshake must be
//                         returned" -> the packet handler returns to idle and
//                        ends the transfer without driving anything.
//
// WHY ENDPOINT 4. USB_C_DEV0_NBPHYSEP is 28 (src/integration/rtl/
// caliptra_ss_top.sv), i.e. 14 OUT/IN pairs, so endpoint numbers 0..14 are all
// backed by real hardware. Endpoint 4 is therefore a genuine endpoint whose
// silence can only be caused by the D bit, and it is used by no other test in
// the tree (only EP0, EP1 and EP2 appear anywhere else). That keeps this test
// distinct from caliptra_ss_usb_hs_dev_unsupported_ep, which probes EP15 - an
// endpoint number with no hardware behind it at all.
//
// THREE DISTINCT CAUSES OF DEVICE SILENCE exist in this IP and must not be
// confused:
//   no hardware behind the endpoint number -> silence (EP15, covered by
//                                             caliptra_ss_usb_hs_dev_unsupported_ep)
//   D = 1, endpoint disabled               -> silence (this test)
//   D = 0 and Active = 0                   -> NAK, which is a handshake and so
//                                             is observably different
// The third case is why the ordering below matters: if the probe arrived before
// the D bit was written, endpoint 4 would NAK instead of staying silent, and
// the host-side verdict would fail loudly rather than pass by accident.
//
// Verdict: FAIL-only. total_errors is never reset; any detected problem
// increments it and the run is failed once at the end with TB_CMD_TEST_FAIL.
// TB_CMD_TEST_PASS is never sent, because it finishes the simulation before the
// UVM final_phase and would mask the host-side verdict.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT              30000

// Endpoint command/status list offset of the EP4 OUT buffer-0 descriptor.
//
// The list layout is fixed: EP0 OUT (0x000), EP0 SETUP (0x004), EP0 IN (0x008),
// reserved (0x00C), then four words (16 bytes) per endpoint number, each being
// OUT buffer 0 / OUT buffer 1 / IN buffer 0 / IN buffer 1. So endpoint N OUT
// buffer 0 sits at 0x010 + (N - 1) * 0x10, which gives 0x010 for EP1 (the
// value used by caliptra_ss_usb_hs_dev_bulk_out), 0x020 for EP2 (used by the
// iso tests) and 0x040 for EP4.
#define USB_EP_LIST_EP4_OUT_OFFSET    0x040u

// Data buffer for EP4 OUT, placed after the EP0 buffers (EP0 uses
// 0x000-0x1FF of the USB SRAM). The endpoint is disabled, so the hardware must
// never touch this buffer; it is programmed only so that the descriptor is a
// realistic, fully formed word rather than a half-filled one.
#define USB_SRAM_EP4_OUT_BUF_OFFSET   0x200u

// Byte count programmed into the descriptor. One HS bulk max packet.
#define USB_EP4_OUT_NBYTES            512u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Never reset. Incremented on every detected problem; drives the single
// TB_CMD_TEST_FAIL at the end of main().
static uint32_t total_errors = 0;

// Mark EP4 OUT as disabled in the endpoint command/status list.
//
// ACTIVE is deliberately left CLEAR. The register documentation allows the D
// field to be modified only while Active is 0, and an endpoint that is both
// armed and disabled is not a legal combination to program. Active = 0 with
// D = 1 is the disabled steady state; Active = 0 with D = 0 would NAK, which
// is exactly the behaviour this test must not see.
static void usb_ep4_out_disable(void) {
    uint32_t ep4_out = USB_EP_ENTRY_DISABLED
                     | USB_EP_ENTRY_NBYTES(USB_EP4_OUT_NBYTES)
                     | USB_EP_ENTRY_ADDR(USB_SRAM_EP4_OUT_BUF_OFFSET);
    uint32_t readback;

    lsu_write_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP4_OUT_OFFSET, ep4_out);
    readback = lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP4_OUT_OFFSET);

    // This marker line is the device-side proof that the endpoint was disabled
    // before the host probe arrived. If the host-side silence check ever fails,
    // compare its timestamp against this line first.
    VPRINTF(LOW, "MCU: EP4 OUT descriptor written 0x%x, reads back 0x%x (D=%d A=%d)\n",
            ep4_out,
            readback,
            (readback & USB_EP_ENTRY_DISABLED) ? 1 : 0,
            (readback & USB_EP_ENTRY_ACTIVE)   ? 1 : 0);

    if ((readback & USB_EP_ENTRY_DISABLED) == 0) {
        VPRINTF(LOW, "MCU: FAIL - EP4 OUT D bit did not stick (descriptor 0x%x)\n", readback);
        total_errors++;
    }
    if (readback & USB_EP_ENTRY_ACTIVE) {
        VPRINTF(LOW, "MCU: FAIL - EP4 OUT ACTIVE is set; a disabled endpoint must not be armed (descriptor 0x%x)\n",
                readback);
        total_errors++;
    }
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    bool     ep4_disabled = false;

    VPRINTF(LOW, "=================\nMCU: USB HS disabled-endpoint test\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
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
                // A bus reset re-initializes the endpoint list, so the D bit
                // has to be re-applied. Clearing the flag makes the loop below
                // program it again.
                if (ep4_disabled) {
                    ep4_disabled = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP4 OUT disable cleared, will re-apply\n");
                }
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

        // Disable EP4 OUT as soon as the device has been configured. Doing it
        // after SET_CONFIGURATION keeps the descriptor write away from the
        // enumeration traffic, and the host sequence only probes after its own
        // enumeration has completed, so the ordering has margin on both sides.
        if (!ep4_disabled &&
            (lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT) &
             DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK) != 0) {
            usb_ep4_out_disable();
            ep4_disabled = true;
        }

        // A disabled endpoint must never raise its endpoint interrupt: the
        // packet handler drops the transaction before any buffer is consumed,
        // so ACTIVE is never cleared by hardware and no EP4 OUT interrupt can
        // be generated. Seeing one means the D bit was not honoured.
        if (reg_data & DEV0_CSR_INTSTAT_EP4OUT_MASK) {
            VPRINTF(LOW, "MCU: FAIL - EP4 OUT interrupt fired for a DISABLED endpoint (INTSTAT=0x%x)\n",
                    reg_data);
            total_errors++;
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP4OUT_MASK);
        }

        if (poll_count % 2000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x ep4_disabled=%d EP4_DESC=0x%x\n",
                    poll_count,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    (int)ep4_disabled,
                    lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP4_OUT_OFFSET));
        }
    }

    // Final state check: the descriptor must still read back as disabled and
    // not armed. The hardware has no path to clear the D bit, so anything else
    // means the probe perturbed the descriptor.
    if (ep4_disabled) {
        uint32_t final_desc = lsu_read_32(USB_DMA_BASE_ADDR + USB_EP_LIST_EP4_OUT_OFFSET);
        VPRINTF(LOW, "MCU: EP4 OUT final descriptor 0x%x\n", final_desc);
        if ((final_desc & USB_EP_ENTRY_DISABLED) == 0) {
            VPRINTF(LOW, "MCU: FAIL - EP4 OUT is no longer disabled at end of test (0x%x)\n",
                    final_desc);
            total_errors++;
        }
        if (final_desc & USB_EP_ENTRY_ACTIVE) {
            VPRINTF(LOW, "MCU: FAIL - EP4 OUT became ACTIVE during the test (0x%x)\n",
                    final_desc);
            total_errors++;
        }
    } else {
        VPRINTF(LOW, "MCU: FAIL - EP4 OUT was never disabled; the device was not configured in time\n");
        total_errors++;
    }

    if (total_errors != 0) {
        VPRINTF(LOW, "MCU: USB HS disabled-endpoint test - %d error(s)\n", total_errors);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    } else {
        VPRINTF(LOW, "MCU: USB HS disabled-endpoint test - all firmware checks passed\n");
    }

    VPRINTF(LOW, "MCU: USB HS disabled-endpoint test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
