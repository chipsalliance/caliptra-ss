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
// Description: USB HS device INTERRUPT endpoint IN/OUT loopback test firmware.
//
// Per docs/usb_int_ep_randomized_test_spec.md: the endpoint number is
// randomized in firmware over EP1..EP7 and published to the UVM host
// sequence over the MCI DEBUG_OUT scratch register (TB_CMD_USB_INT_EP). All
// EP-list and buffer offsets are computed from the endpoint number. Define
// USB_INT_EP_FIXED to override randomization for debug. The EP command/status
// list is a table of 16-byte (0x10) blocks indexed by LOGICAL endpoint, so
// each endpoint consumes 0x10 bytes (0x10*n OUT command word, +8 IN command
// word). With the EP1..EP7 clamp the worst case is EP7 (OUT slot 0x70, IN word
// 0x78), which stays below the SETUP buffer at 0x100; no SRAM relocation is
// required and a runtime boundary assert guards it.

//
// Flow:
//   1. Boot MCU and USB core in HS device mode.
//   2. Service enumeration on EP0 (bus reset + SETUP packets).
//   3. Arm EPn OUT as an INTERRUPT endpoint (T=1, RF=1) for 64 bytes.
//   4. On the EPn OUT completion interrupt, copy the received payload into the
//      EPn IN buffer and arm EPn IN (bit 26 left clear - see note below).
//   5. When hardware clears the Active bit of the EPn IN entry the host has
//      collected the loopback data: declare PASS.
//
// NXP IP_3511HS EP command/status entry bit fields (Integration Guide 4.2.3):
//   [31] A   = Active
//   [26] T   = 1 for periodic (isochronous/interrupt) on OUT entries
//   [27] RF  = 0 for isochronous (when T=1), 1 for INTERRUPT (when T=1)
//   [25:11]  = NBytes
//   [10:0]   = AddrOffset (buffer byte address >> 6)
//   NOTE: bit 26 on IN entries is the data Toggle bit (0=DATA0), NOT the Type
//         bit. Do NOT set USB_EP_ENTRY_TYPE_PERIODIC on IN entries. This
//         asymmetry is a hardware property, not an oversight.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Endpoint number is randomized in firmware over the hardware-supported data
// range EP1..EP7 (physical-endpoint ceiling C_NBPHYSEP=14, EP0 reserved for
// control) and published to the UVM host sequence over the MCI DEBUG_OUT
// scratch register.
// Define USB_INT_EP_FIXED to a value in 1..7 to override randomization
// (useful for reproducing a specific EP during debug). Left commented out for
// normal randomized runs; the fixed-EP2 debug case was verified PASSING (OUT
// data check + IN loopback) after the 0x10*n stride and deferred-arm fixes.
// #define USB_INT_EP_FIXED           2u


// Interrupt transfer size. 64 bytes is legal for both FS and HS interrupt
// endpoints (usb_dma.m.vhdl maxpacket encoding "00"), so the same firmware
// body works at either speed.
#define USB_INT_TRANSFER_BYTES        64u

// Bounded so the test terminates (fails gracefully) instead of hanging when
// the interrupt endpoint never completes, but large enough to fully cover
// USBDC0 enumeration (which completes ~450us / well past the first ~20000
// polls). An earlier value of 20000 halted the MCU BEFORE enumeration
// finished, which starved Dev:2 EP0 control transfers and produced
// device_response_timeout_check_Dev2_EP0 errors instead of a clean
// interrupt-loopback pass/fail. Set to 100000 for full randomized runs.
#define USB_POLL_TIMEOUT              100000


// EP command/status list offsets, derived from the endpoint number per
// Integration Guide 4.2.1. The list is a table of 16-byte (0x10) blocks
// indexed by LOGICAL endpoint: block n holds the OUT command/status word at
// 0x10*n and the IN command/status word at 0x10*n + 8.
//
// This matches the actual literal offsets the known-good iso/bulk tests write
// (caliptra_ss_usb_hs_dev_iso_out.c: EP2 OUT = 0x020, IN = 0x028), which for
// EP2 is 0x10*2 and 0x10*2 + 8. (Note: a prose comment in that iso file writes
// the formula as "0x10*(2*n)", but that is arithmetically inconsistent with
// its own 0x020 literal - 0x10*(2*2) would be 0x040 - so the literal, not the
// prose, is authoritative.)
//
// Confirmed against the RTL in usb2/.../RTL/RTL/usb_dma.m.vhdl, which builds
// the command/status list address as:
//   epinfo_addr[7:4] = epnr        (EP number, weight 0x10)
//   epinfo_addr[3]   = epdir       (0=OUT +0x0, 1=IN +0x8)
//   epinfo_addr[2]   = buf select  (buf0 +0x0, buf1 +0x4)
//   epinfo_addr[1:0] = 0
// so the DMA fetches EP(n) OUT from base + n*0x10 and EP(n) IN from
// base + n*0x10 + 8 (EP2: OUT=0x20, IN=0x28).
//
// NOTE: a prior version of THIS file used a 0x10*(2*n) stride (0x040 for EP2).
// That was proven wrong on hardware: the device DMA fetches the EP2 OUT
// command word from base+0x020, but firmware armed base+0x040, so the DMA read
// an all-zero descriptor. The EPINFO handshake returned ACTIVE=0 / ISO=0 /
// RATEFEEDBACKMODE=0 / NBYTES=0, so the device NAKed every OUT token; the OUT
// never completed and the IN loopback then read an untouched (all-zero)
// buffer. The correct stride is 0x10*n. Do not revert to 0x10*(2*n).
//   EP(n) OUT command/status word at 0x10 * n
//   EP(n) IN  command/status word at 0x10 * n + 8
#define USB_EP_LIST_OUT_OFFSET(n)     (0x10u * (n))
#define USB_EP_LIST_IN_BUF0_OFFSET(n) (0x10u * (n) + 8u)




// Data buffers. Kept identical to the known-good isochronous map: EP0 owns
// 0x000-0x1FF and the 0x200-0x5FF region is unused by this test.
#define USB_SRAM_INT_OUT_BUF_OFFSET   0x600u
#define USB_SRAM_INT_IN_BUF_OFFSET    0xA00u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm the OUT direction of the selected endpoint as INTERRUPT (T=1, RF=1)
// and unmask its completion interrupt.
static void usb_int_ep_out_arm(uint32_t ep) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_TYPE_PERIODIC
                   | USB_EP_ENTRY_RF_INT
                   | USB_EP_ENTRY_NBYTES(USB_INT_TRANSFER_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + USB_SRAM_INT_OUT_BUF_OFFSET);
    uint32_t slot = USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_OUT_OFFSET(ep);
    lsu_write_32(slot, entry);

    // INTSTAT/INTEN bit index for EP(n) OUT is 2*n (EP0 OUT = bit 0).
    uint32_t inten = lsu_read_32(USB_DEV_INTEN);
    lsu_write_32(USB_DEV_INTEN, inten | (1u << (2u * ep)));

    // Readback: confirm the command word actually landed in the device
    // command/status SRAM at the physical-slot address we computed. If the
    // stride/offset is wrong this reads back 0 (or a stale value) instead of
    // the armed entry, which pinpoints an addressing bug vs a datapath issue.
    uint32_t rb = lsu_read_32(slot);
    VPRINTF(LOW,
        "MCU: EP%d OUT armed as INTERRUPT (T=1,RF=1), %d bytes; "
        "slot=0x%x wrote=0x%x readback=0x%x%s\n",
        ep, USB_INT_TRANSFER_BYTES, slot, entry, rb,
        (rb == entry) ? "" : " <<< MISMATCH");

}

// Arm the IN direction of the selected endpoint. Bit 26 is the data Toggle
// bit on IN entries, so TYPE_PERIODIC must NOT be set here.
static void usb_int_ep_in_arm(uint32_t ep) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_NBYTES(USB_INT_TRANSFER_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + USB_SRAM_INT_IN_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_IN_BUF0_OFFSET(ep), entry);

    VPRINTF(LOW, "MCU: EP%d IN armed with %d loopback bytes\n",
            ep, USB_INT_TRANSFER_BYTES);
}

void main(void) {
    uint32_t reg_data;
    uint32_t intstat;
    uint32_t poll_count;
    uint32_t i;
    uint32_t int_ep;
    uint32_t ep_out_int_mask;
    bool     out_armed     = false;
    bool     loopback_done = false;
    bool     all_done      = false;

#ifdef USB_INT_EP_FIXED
    int_ep = USB_INT_EP_FIXED;
#else
    // Randomize the interrupt endpoint number over the hardware-supported
    // range EP1..EP7.
    //
    // Physical-endpoint ceiling (NOT logical EP15): the IP maps a logical
    // endpoint+direction to a physical slot as phys = 2*epnr + epdir, and
    // usb_dma.m.vhdl only honors the request when phys <= C_NBPHYSEP+1. This
    // DUT instantiates the IP at the default C_NBPHYSEP = 14 (see
    // caliptra_ss_top.sv, which does not override the generic), so the limit
    // is phys <= 15, i.e. logical EP0..EP7 in both directions. Requesting a
    // higher endpoint forces endpoint_nr_dir to 0 in the DMA, silently
    // aliasing the transfer onto physical slot 0 (EP0 OUT); the target EP's
    // command/status Active bit is then never cleared and firmware hangs.
    // Clamp to EP1..EP7 to stay within the compiled physical-endpoint set.
    int_ep = (xorshift32() % 7u) + 1u;
#endif


    // Boundary guard: the EP command/status list is a contiguous table at
    // offset 0 indexed by logical endpoint, so a logical EP's OUT slot starts
    // at 0x10*n and its IN word at +8. The selected EP's slot must end at or
    // before the SETUP buffer at 0x100 so the list does not overrun EP0's
    // control/data buffers. With the EP1..EP7 clamp the worst case is EP7 (OUT
    // slot 0x70..0x7F), which fits below 0x100.

    if ((USB_EP_LIST_OUT_OFFSET(int_ep) + 0x10u) > USB_SRAM_SETUP_BUF_OFFSET) {
        VPRINTF(FATAL,
            "MCU: EP%d list slot 0x%x overruns SETUP buffer 0x%x - aborting\n",
            int_ep, USB_EP_LIST_OUT_OFFSET(int_ep), USB_SRAM_SETUP_BUF_OFFSET);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        while (1);
    }

    ep_out_int_mask = (1u << (2u * int_ep));

    VPRINTF(LOW,
        "=================\nMCU: USB HS device INTERRUPT EP loopback test (EP%d)\n=================\n\n",
        int_ep);

    // Publish the randomized endpoint number to the UVM host sequence via the
    // MCI DEBUG_OUT scratch register. The payload is packed as
    // { ep_num[15:8], TB_CMD_USB_INT_EP[7:0] }; the opcode 0xf3 lies outside
    // the printable console window (0x06..0x7e) so it does not corrupt the log.
    // The TB decode in caliptra_ss_top_tb_services.sv broadcasts it into the
    // uvm_config_db under "usb_int_ep_num".
    lsu_write_32(SOC_MCI_TOP_MCI_REG_DEBUG_OUT,
                 (int_ep << 8) | TB_CMD_USB_INT_EP);
    VPRINTF(LOW, "MCU: randomized interrupt endpoint = EP%d\n", int_ep);

    boot_mcu();
    boot_usb_core();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !all_done;
         poll_count++) {

        // Any bus reset clears the Active bit on ALL endpoints and
        // usb_handle_bus_reset() only restores EP0, so the interrupt endpoint
        // must be re-armed explicitly whenever DRES_C was observed.
        uint32_t prev_dres = lsu_read_32(USB_DEV_DEVCMDSTAT)
                             & USBHSD_DEVCMDSTAT_DRES_C_MASK;
        usb_handle_bus_reset();
        if (prev_dres && out_armed && !loopback_done) {
            VPRINTF(LOW, "MCU: Bus reset - re-arming EP%d OUT\n", int_ep);
            usb_int_ep_out_arm(int_ep);
        }

        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);

        // EP0 OUT: enumeration / control transfers.
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
            }
        }

        // Arm the interrupt endpoint only AFTER the device has been assigned
        // its bus address (DEVCMDSTAT.DEV_ADDR != 0). Arming on the very first
        // SETUP - i.e. while the device is still at address 0 mid-enumeration -
        // disturbed the EP0 control machine so the IP NAKed the immediately
        // following SET_ADDRESS SETUP (a protocol violation: a SETUP must never
        // be NAKed). That left the device stuck at address 0, so every later
        // addr=2 control transfer timed out (device_response_timeout_check_
        // Dev2_EP0). Deferring the arm until DEV_ADDR is programmed keeps EP0
        // enumeration completely undisturbed. The address field is nonzero only
        // after SET_ADDRESS has been serviced, which is exactly the safe point.
        if (!out_armed
            && (lsu_read_32(USB_DEV_DEVCMDSTAT)
                & USBHSD_DEVCMDSTAT_DEV_ADDR_MASK) != 0u) {
            usb_int_ep_out_arm(int_ep);
            out_armed = true;
        }


        // EP0 IN: status-phase completion.
        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

        // Interrupt OUT completion: verify the payload, then loop it back.
        //
        // Completion is detected by hardware CLEARING the Active bit of the
        // OUT entry, not by an INTSTAT bit. The INTSTAT bit index for an
        // arbitrary endpoint is not reliably 2*n on this IP, and relying on it
        // made the branch never fire. The Active bit is defined per the EP
        // command/status entry format and is direction- and EP-agnostic, so it
        // is the correct completion signal for the randomized-EP case too.
        // The INTSTAT bit is still write-1-cleared opportunistically to keep
        // the status register from latching up.
        if (out_armed && !loopback_done) {
            uint32_t entry = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                         + USB_EP_LIST_OUT_OFFSET(int_ep));

            if (!(entry & USB_EP_ENTRY_ACTIVE)) {
                uint32_t residual;
                uint32_t errors = 0;

                if (intstat & ep_out_int_mask)
                    lsu_write_32(USB_DEV_INTSTAT, ep_out_int_mask);

                residual = (entry >> 11) & 0x7FFFu;

                VPRINTF(LOW,
                    "MCU: EP%d INTERRUPT OUT done - received %d bytes (residual=%d)\n",
                    int_ep, USB_INT_TRANSFER_BYTES - residual, residual);

                // Expected host pattern: byte[i] = i.
                for (i = 0; i < USB_INT_TRANSFER_BYTES; i++) {
                    uint32_t word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                                + USB_SRAM_INT_OUT_BUF_OFFSET
                                                + (i & ~3u));
                    uint8_t  actual   = (uint8_t)((word >> ((i & 3u) * 8u)) & 0xFFu);
                    uint8_t  expected = (uint8_t)(i & 0xFFu);
                    if (actual != expected) {
                        if (errors < 8)
                            VPRINTF(LOW,
                                "MCU: OUT MISMATCH byte[%d]: got 0x%x exp 0x%x\n",
                                i, actual, expected);
                        errors++;
                    }
                }
                if (errors == 0)
                    VPRINTF(LOW, "MCU: EP%d INTERRUPT OUT data check PASSED\n",
                            int_ep);
                else
                    VPRINTF(LOW,
                        "MCU: EP%d INTERRUPT OUT data check FAILED (%d errors)\n",
                        int_ep, errors);

                // Copy the received payload into the IN buffer and arm IN.
                for (i = 0; i < USB_INT_TRANSFER_BYTES; i += 4) {
                    uint32_t word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                                + USB_SRAM_INT_OUT_BUF_OFFSET + i);
                    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                                 + USB_SRAM_INT_IN_BUF_OFFSET + i, word);
                }
                usb_int_ep_in_arm(int_ep);
                loopback_done = true;
            }
        }


        // Interrupt IN completion: unlike isochronous IN, an interrupt IN is
        // ACKed by the host, so hardware does clear the Active bit here.
        if (loopback_done) {
            uint32_t in_entry = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                            + USB_EP_LIST_IN_BUF0_OFFSET(int_ep));
            if (!(in_entry & USB_EP_ENTRY_ACTIVE)) {
                VPRINTF(LOW,
                    "MCU: USB HS dev INTERRUPT EP%d loopback PASSED\n", int_ep);
                all_done = true;
            }
        }

        if (poll_count % 5000 == 0 && poll_count > 0) {
            VPRINTF(LOW,
                "MCU: [poll %d] DEVCMDSTAT=0x%x INTSTAT=0x%x\n",
                poll_count, lsu_read_32(USB_DEV_DEVCMDSTAT),
                lsu_read_32(USB_DEV_INTSTAT));
        }
    }

    if (!all_done)
        VPRINTF(LOW,
            "MCU: USB HS dev INTERRUPT EP%d loopback TIMEOUT (out_armed=%d loopback_done=%d)\n",
            int_ep, (uint32_t)out_armed, (uint32_t)loopback_done);

    VPRINTF(LOW, "MCU: USB HS device INTERRUPT EP loopback test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
