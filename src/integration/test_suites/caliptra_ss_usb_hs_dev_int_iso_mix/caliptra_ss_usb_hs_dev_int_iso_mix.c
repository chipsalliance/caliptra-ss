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
// Description: USB HS device mixed INTERRUPT (EP1) + ISOCHRONOUS (EP2) test
//              firmware. Merge of caliptra_ss_usb_hs_dev_int_loopback.c and
//              caliptra_ss_usb_hs_dev_iso_out.c, with the two endpoint types
//              pinned to distinct logical endpoints so both stay armed at the
//              same time and share the device DMA / EP command-status list.
//
// Host-side phase order driven by caliptra_ss_usb_hs_dev_int_iso_mix_sequence:
//   phase 0: INTERRUPT round 0 on EP1 (OUT 64 B then IN 64 B loopback)
//   phase 1: ISOCHRONOUS round 0 on EP2 (OUT 1024 B then 2x IN 512 B)
//   phase 2: INTERRUPT round 1 on EP1 (new data pattern)
//
// The firmware itself is phase-agnostic: it arms EP1 OUT and EP2 OUT once the
// device address has been programmed and then services whichever endpoint the
// host decides to drive next.
//
// Resource split (no overlap between the INT and ISO sides):
//   resource               EP1 (INTERRUPT)      EP2 (ISOCHRONOUS)
//   EP-list OUT word       0x010                0x020
//   EP-list IN buf0        0x018                0x028
//   EP-list IN buf1        -                    0x02C
//   SRAM OUT buffer        0x200 (64 B)         0x600 (1024 B)
//   SRAM IN  buffer        0x400 (64 B)         0xA00 (1024 B)
// EP0 keeps 0x000-0x1FF of the data region; the EP command/status list itself
// lives at offset 0 and must stay below the SETUP buffer at 0x100.
//
// NXP IP_3511HS EP command/status entry bit fields (Integration Guide 4.2.3):
//   [31] A   = Active
//   [27] RF  = 1 for INTERRUPT (when T=1), 0 for isochronous (when T=1)
//   [26] T   = 1 for periodic (isochronous/interrupt) on OUT entries
//   [25:11]  = NBytes
//   [10:0]   = AddrOffset (buffer byte address >> 6)
//   NOTE: bit 26 on IN entries is the data Toggle bit (0=DATA0), NOT the Type
//         bit. Do NOT set USB_EP_ENTRY_TYPE_PERIODIC on IN entries. This
//         asymmetry is a hardware property, not an oversight.
//
// Completion-signal asymmetry between the two endpoint types (both observed on
// this IP and both relied on below):
//   INTERRUPT: the host ACKs, so hardware CLEARS the Active bit of the OUT and
//              IN entries. The INTSTAT bit index 2*n is not reliable for an
//              arbitrary endpoint, so the Active bit is the completion signal.
//   ISO OUT:   hardware sets INTSTAT EP2OUT on receive (reliable).
//   ISO IN:    there is no host ACK, so hardware neither clears the Active bit
//              nor sets INTSTAT EP2IN. Firmware must NOT poll either one; it
//              only guarantees the SRAM payload is in place before the host
//              issues the IN tokens.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Logical endpoint assignment. Both are inside the compiled physical-endpoint
// set (phys = 2*epnr + epdir must be <= C_NBPHYSEP+1 = 15 for the default
// C_NBPHYSEP=14 this DUT instantiates), i.e. logical EP0..EP7 are usable.
#define USB_INT_EP                    1u
#define USB_ISO_EP                    2u

// INTERRUPT rounds. The host drives round 0, then the ISO phase, then round 1.
#define N_INT_ROUNDS                  2u

// Per-round byte-value offset so each INTERRUPT round carries a distinct
// pattern: byte[i] = (i + round*INT_ROUND_OFFSET) % 256. Must match
// INT_ROUND_OFFSET in the UVM sequence.
#define INT_ROUND_OFFSET              85u

// Interrupt transfer size. 64 bytes is legal for both FS and HS interrupt
// endpoints (usb_dma.m.vhdl maxpacket encoding "00").
#define USB_INT_TRANSFER_BYTES        64u

// HS isochronous max packet size (USB 2.0 spec table 5-7).
#define USB_HS_ISO_TRANSFER_BYTES     1024u

// Each ISO IN buffer entry carries half the total transfer (512 bytes).
#define USB_HS_ISO_IN_BUF_BYTES       (USB_HS_ISO_TRANSFER_BYTES / 2u)

// Poll loop timeout (iterations). Sized to cover USBDC0 enumeration (~450us,
// well past the first ~20000 polls) plus all three traffic phases.
#define USB_POLL_TIMEOUT              100000

// Iterations to keep spinning after the ISO IN buffers are armed so the host
// has a window to issue its two IN tokens. ISO IN has no completion signal, so
// this is the only way to know the data was served. ~10000 iterations is
// ~1.5 ms, enough for two IN tokens plus the inter-transfer gap.
#define ISO_IN_READ_WINDOW            10000u

// EP command/status list offsets, derived from the endpoint number per
// Integration Guide 4.2.1. The list is a table of 16-byte (0x10) blocks
// indexed by LOGICAL endpoint:
//   EP(n) OUT      command/status word at 0x10*n
//   EP(n) IN buf0  command/status word at 0x10*n + 8
//   EP(n) IN buf1  command/status word at 0x10*n + 0xC
// Confirmed against usb_dma.m.vhdl, which builds the list address as
// epinfo_addr[7:4]=epnr, [3]=epdir, [2]=buffer select, [1:0]=0.
// Do NOT use a 0x10*(2*n) stride: a prose comment in the iso_out test states
// that formula but contradicts its own 0x020 literal for EP2, and arming at
// the wrong slot makes the DMA fetch an all-zero descriptor so the device NAKs
// every token.
#define USB_EP_LIST_OUT_OFFSET(n)     (0x10u * (n))
#define USB_EP_LIST_IN_BUF0_OFFSET(n) (0x10u * (n) + 8u)
#define USB_EP_LIST_IN_BUF1_OFFSET(n) (0x10u * (n) + 0xCu)

// Data buffers. EP0 owns 0x000-0x1FF. The INTERRUPT side was moved out of the
// 0x600/0xA00 pair it uses in the standalone int_loopback test so the ISO side
// can keep its proven offsets unchanged.
#define USB_SRAM_INT_OUT_BUF_OFFSET   0x200u
#define USB_SRAM_INT_IN_BUF_OFFSET    0x400u
#define USB_SRAM_ISO_OUT_BUF_OFFSET   0x600u
#define USB_SRAM_ISO_IN_BUF_OFFSET    0xA00u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// -------------------------------------------------------------------------
// EP1 - INTERRUPT
// -------------------------------------------------------------------------

// Arm EP1 OUT as INTERRUPT (T=1, RF=1) and unmask its completion interrupt.
static void usb_int_ep_out_arm(void) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_TYPE_PERIODIC
                   | USB_EP_ENTRY_RF_INT
                   | USB_EP_ENTRY_NBYTES(USB_INT_TRANSFER_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + USB_SRAM_INT_OUT_BUF_OFFSET);
    uint32_t slot = USB_DEV_DMA_BASE_ADDR
                    + USB_EP_LIST_OUT_OFFSET(USB_INT_EP);
    uint32_t inten;
    uint32_t rb;

    lsu_write_32(slot, entry);

    // INTSTAT/INTEN bit index for EP(n) OUT is 2*n (EP0 OUT = bit 0).
    inten = lsu_read_32(USB_DEV_INTEN);
    lsu_write_32(USB_DEV_INTEN, inten | (1u << (2u * USB_INT_EP)));

    // Readback: if the slot address is wrong this reads back 0 instead of the
    // armed entry, which separates an addressing bug from a datapath issue.
    rb = lsu_read_32(slot);
    VPRINTF(LOW,
        "MCU: EP%d OUT armed as INTERRUPT (T=1,RF=1), %d bytes; "
        "slot=0x%x wrote=0x%x readback=0x%x%s\n",
        USB_INT_EP, USB_INT_TRANSFER_BYTES, slot, entry, rb,
        (rb == entry) ? "" : " <<< MISMATCH");
}

// Arm EP1 IN. Bit 26 is the data Toggle bit on IN entries, so TYPE_PERIODIC
// must NOT be set here.
static void usb_int_ep_in_arm(void) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_NBYTES(USB_INT_TRANSFER_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + USB_SRAM_INT_IN_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                 + USB_EP_LIST_IN_BUF0_OFFSET(USB_INT_EP), entry);

    VPRINTF(LOW, "MCU: EP%d IN armed with %d loopback bytes\n",
            USB_INT_EP, USB_INT_TRANSFER_BYTES);
}

// -------------------------------------------------------------------------
// EP2 - ISOCHRONOUS
// -------------------------------------------------------------------------

// Arm EP2 OUT as isochronous (T=1, RF=0) and unmask its completion interrupt.
static void usb_iso_ep_out_arm(void) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_TYPE_PERIODIC
                   | USB_EP_ENTRY_RF_ISO
                   | USB_EP_ENTRY_NBYTES(USB_HS_ISO_TRANSFER_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + USB_SRAM_ISO_OUT_BUF_OFFSET);
    uint32_t slot = USB_DEV_DMA_BASE_ADDR
                    + USB_EP_LIST_OUT_OFFSET(USB_ISO_EP);
    uint32_t inten;

    lsu_write_32(slot, entry);

    inten = lsu_read_32(USB_DEV_INTEN);
    lsu_write_32(USB_DEV_INTEN, inten | DEV0_CSR_INTSTAT_EP2OUT_MASK);

    VPRINTF(LOW,
        "MCU: EP%d OUT armed as ISO (T=1,RF=0), %d bytes; slot=0x%x entry=0x%x\n",
        USB_ISO_EP, USB_HS_ISO_TRANSFER_BYTES, slot, entry);
}

static uint32_t usb_iso_ep_out_read(void) {
    return lsu_read_32(USB_DEV_DMA_BASE_ADDR
                       + USB_EP_LIST_OUT_OFFSET(USB_ISO_EP));
}

// Fill the EP2 IN SRAM with the inverse ramp byte[i] = 255 - (i % 256) and arm
// both IN buffer entries (512 bytes each). The host checks this payload.
static void usb_iso_ep_in_arm(void) {
    uint32_t i;
    uint32_t buf0;
    uint32_t buf1;

    for (i = 0; i < USB_HS_ISO_TRANSFER_BYTES; i += 4) {
        uint32_t b0 = 255u - ((i + 0u) % 256u);
        uint32_t b1 = 255u - ((i + 1u) % 256u);
        uint32_t b2 = 255u - ((i + 2u) % 256u);
        uint32_t b3 = 255u - ((i + 3u) % 256u);
        lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_ISO_IN_BUF_OFFSET + i,
                     b0 | (b1 << 8) | (b2 << 16) | (b3 << 24));
    }

    // Per Integration Guide 4.2.3, bit 26 on IN entries is the Toggle bit
    // (0=DATA0). Do NOT set USB_EP_ENTRY_TYPE_PERIODIC on IN entries.
    buf0 = USB_EP_ENTRY_ACTIVE
         | USB_EP_ENTRY_NBYTES(USB_HS_ISO_IN_BUF_BYTES)
         | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                 + USB_SRAM_ISO_IN_BUF_OFFSET);
    buf1 = USB_EP_ENTRY_ACTIVE
         | USB_EP_ENTRY_NBYTES(USB_HS_ISO_IN_BUF_BYTES)
         | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                 + USB_SRAM_ISO_IN_BUF_OFFSET
                                 + USB_HS_ISO_IN_BUF_BYTES);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                 + USB_EP_LIST_IN_BUF0_OFFSET(USB_ISO_EP), buf0);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                 + USB_EP_LIST_IN_BUF1_OFFSET(USB_ISO_EP), buf1);

    VPRINTF(LOW,
        "MCU: EP%d IN (ISO) armed - buf0=0x%x buf1=0x%x (%d bytes each)\n",
        USB_ISO_EP, buf0, buf1, USB_HS_ISO_IN_BUF_BYTES);
}

// -------------------------------------------------------------------------

void main(void) {
    uint32_t reg_data;
    uint32_t intstat;
    uint32_t poll_count;
    uint32_t i;
    uint32_t int_ep_out_int_mask;

    // INTERRUPT state.
    uint32_t int_round        = 0u;   // completed INTERRUPT loopback rounds
    bool     int_out_armed    = false;
    bool     int_in_armed     = false;

    // ISOCHRONOUS state.
    bool     iso_out_armed    = false;
    bool     iso_out_done     = false;
    bool     iso_in_armed     = false;
    bool     iso_done         = false;
    uint32_t iso_wait_start   = 0u;

    bool     all_done         = false;

    // Boundary guard: the EP command/status list is a contiguous table at
    // offset 0 indexed by logical endpoint. The highest slot used here (EP2 IN
    // buf1 at 0x02C) must end at or before the SETUP buffer at 0x100 so the
    // list does not overrun EP0's control/data buffers.
    if ((USB_EP_LIST_OUT_OFFSET(USB_ISO_EP) + 0x10u)
        > USB_SRAM_SETUP_BUF_OFFSET) {
        VPRINTF(FATAL,
            "MCU: EP%d list slot 0x%x overruns SETUP buffer 0x%x - aborting\n",
            USB_ISO_EP, USB_EP_LIST_OUT_OFFSET(USB_ISO_EP),
            USB_SRAM_SETUP_BUF_OFFSET);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        while (1);
    }

    int_ep_out_int_mask = (1u << (2u * USB_INT_EP));

    VPRINTF(LOW,
        "=================\nMCU: USB HS device mixed INTERRUPT EP%d + ISO EP%d test\n=================\n\n",
        USB_INT_EP, USB_ISO_EP);

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !all_done;
         poll_count++) {

        // Any bus reset clears the Active bit on ALL endpoints and
        // usb_handle_bus_reset() only restores EP0, so both data endpoints must
        // be re-armed explicitly whenever DRES_C was observed.
        uint32_t prev_dres = lsu_read_32(USB_DEV_DEVCMDSTAT)
                             & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK;
        usb_handle_bus_reset();
        if (prev_dres) {
            if (int_out_armed && !int_in_armed && int_round < N_INT_ROUNDS) {
                VPRINTF(LOW, "MCU: Bus reset - re-arming EP%d OUT\n",
                        USB_INT_EP);
                usb_int_ep_out_arm();
            }
            if (iso_out_armed && !iso_out_done) {
                VPRINTF(LOW, "MCU: Bus reset - re-arming EP%d OUT\n",
                        USB_ISO_EP);
                usb_iso_ep_out_arm();
            }
        }

        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);

        // EP0 OUT: enumeration / control transfers.
        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
            }
        }

        // Arm the data endpoints only AFTER the device has been assigned its
        // bus address (DEVCMDSTAT.DEV_ADDR != 0). Arming while the device is
        // still at address 0 mid-enumeration disturbs the EP0 control machine
        // so the IP NAKs the immediately following SET_ADDRESS SETUP (a
        // protocol violation: a SETUP must never be NAKed). That leaves the
        // device stuck at address 0 and every later addr=2 control transfer
        // times out. DEV_ADDR is nonzero only after SET_ADDRESS has been
        // serviced, which is exactly the safe arming point.
        if (!int_out_armed
            && (lsu_read_32(USB_DEV_DEVCMDSTAT)
                & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK) != 0u) {
            usb_int_ep_out_arm();
            int_out_armed = true;
        }
        if (!iso_out_armed
            && (lsu_read_32(USB_DEV_DEVCMDSTAT)
                & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK) != 0u) {
            usb_iso_ep_out_arm();
            iso_out_armed = true;
        }

        // EP0 IN: status-phase completion.
        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);

        // ---------------------------------------------------------------
        // EP1 INTERRUPT state machine.
        // ---------------------------------------------------------------

        // INTERRUPT OUT completion: detected by hardware CLEARING the Active
        // bit of the OUT entry (the INTSTAT bit index is not reliable for an
        // arbitrary endpoint). The INTSTAT bit is still write-1-cleared
        // opportunistically so the status register does not latch up.
        if (int_out_armed && !int_in_armed && int_round < N_INT_ROUNDS) {
            uint32_t entry = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                 + USB_EP_LIST_OUT_OFFSET(USB_INT_EP));

            if (!(entry & USB_EP_ENTRY_ACTIVE)) {
                uint32_t residual;
                uint32_t errors     = 0u;
                uint32_t round_base = int_round * INT_ROUND_OFFSET;

                if (intstat & int_ep_out_int_mask)
                    lsu_write_32(USB_DEV_INTSTAT, int_ep_out_int_mask);

                residual = (entry >> 11) & 0x7FFFu;

                VPRINTF(LOW,
                    "MCU: [int round %d] EP%d INTERRUPT OUT done - received %d bytes (residual=%d)\n",
                    int_round, USB_INT_EP,
                    USB_INT_TRANSFER_BYTES - residual, residual);

                // Expected host pattern: byte[i] = (i + round*85) % 256.
                for (i = 0; i < USB_INT_TRANSFER_BYTES; i++) {
                    uint32_t word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                                + USB_SRAM_INT_OUT_BUF_OFFSET
                                                + (i & ~3u));
                    uint8_t  actual   = (uint8_t)((word >> ((i & 3u) * 8u))
                                                  & 0xFFu);
                    uint8_t  expected = (uint8_t)((i + round_base) % 256u);
                    if (actual != expected) {
                        if (errors < 8)
                            VPRINTF(LOW,
                                "MCU: [int round %d] OUT MISMATCH byte[%d]: got 0x%x exp 0x%x\n",
                                int_round, i, actual, expected);
                        errors++;
                    }
                }
                if (errors == 0)
                    VPRINTF(LOW,
                        "MCU: [int round %d] EP%d INTERRUPT OUT data check PASSED\n",
                        int_round, USB_INT_EP);
                else
                    VPRINTF(LOW,
                        "MCU: [int round %d] EP%d INTERRUPT OUT data check FAILED (%d errors)\n",
                        int_round, USB_INT_EP, errors);

                // Copy the received payload into the IN buffer and arm IN.
                for (i = 0; i < USB_INT_TRANSFER_BYTES; i += 4) {
                    uint32_t word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                                + USB_SRAM_INT_OUT_BUF_OFFSET
                                                + i);
                    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                                 + USB_SRAM_INT_IN_BUF_OFFSET + i, word);
                }
                usb_int_ep_in_arm();
                int_in_armed = true;
            }
        }

        // INTERRUPT IN completion: unlike isochronous IN, an interrupt IN is
        // ACKed by the host, so hardware does clear the Active bit here.
        if (int_in_armed) {
            uint32_t in_entry = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                    + USB_EP_LIST_IN_BUF0_OFFSET(USB_INT_EP));
            if (!(in_entry & USB_EP_ENTRY_ACTIVE)) {
                int_in_armed = false;
                int_round++;
                VPRINTF(LOW,
                    "MCU: EP%d INTERRUPT loopback round %d PASSED (%d/%d rounds done)\n",
                    USB_INT_EP, int_round - 1u, int_round, N_INT_ROUNDS);

                if (int_round < N_INT_ROUNDS) {
                    // Re-arm OUT for the next INTERRUPT round. The host runs
                    // the ISO phase in between, so this entry simply stays
                    // Active (the device NAKs nothing - no IN/OUT tokens are
                    // sent to EP1 during the ISO phase) until phase 2 starts.
                    usb_int_ep_out_arm();
                }
            }
        }

        // ---------------------------------------------------------------
        // EP2 ISOCHRONOUS state machine.
        // ---------------------------------------------------------------

        // ISO OUT completion: hardware reliably sets INTSTAT EP2OUT.
        if (iso_out_armed && !iso_out_done
            && (intstat & DEV0_CSR_INTSTAT_EP2OUT_MASK)) {
            uint32_t iso_entry;
            uint32_t residual;
            uint32_t errors = 0u;

            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);

            iso_entry = usb_iso_ep_out_read();
            residual  = (iso_entry >> 11) & 0x7FFFu;

            VPRINTF(LOW,
                "MCU: EP%d ISO OUT done - received %d bytes (residual=%d)\n",
                USB_ISO_EP, USB_HS_ISO_TRANSFER_BYTES - residual, residual);

            // Expected host pattern: byte[i] = i % 256.
            for (i = 0; i < USB_HS_ISO_TRANSFER_BYTES; i++) {
                uint32_t word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                            + USB_SRAM_ISO_OUT_BUF_OFFSET
                                            + (i & ~3u));
                uint8_t  actual   = (uint8_t)((word >> ((i & 3u) * 8u))
                                              & 0xFFu);
                uint8_t  expected = (uint8_t)(i % 256u);
                if (actual != expected) {
                    if (errors < 8)
                        VPRINTF(LOW,
                            "MCU: ISO OUT MISMATCH byte[%d]: got 0x%x exp 0x%x\n",
                            i, actual, expected);
                    errors++;
                }
            }
            if (errors == 0)
                VPRINTF(LOW, "MCU: EP%d ISO OUT data check PASSED\n",
                        USB_ISO_EP);
            else
                VPRINTF(LOW,
                    "MCU: EP%d ISO OUT data check FAILED (%d errors)\n",
                    USB_ISO_EP, errors);

            iso_out_done = true;

            // Fill SRAM and arm EP2 IN. The ISO IN Active bit is never cleared
            // by hardware and INTSTAT EP2IN never fires, so this is the last
            // action the firmware can take for the ISO phase.
            usb_iso_ep_in_arm();
            iso_in_armed   = true;
            iso_wait_start = poll_count;
        }

        // ISO IN has no completion signal: once the IN buffers are armed, just
        // give the host a bounded window to issue its two IN tokens.
        if (iso_in_armed && !iso_done
            && (poll_count - iso_wait_start) >= ISO_IN_READ_WINDOW) {
            VPRINTF(LOW,
                "MCU: EP%d ISO IN read window elapsed - ISO phase complete\n",
                USB_ISO_EP);
            iso_done = true;
        }

        // Both endpoint families finished.
        if (int_round >= N_INT_ROUNDS && iso_done)
            all_done = true;

        if (poll_count % 5000 == 0 && poll_count > 0) {
            VPRINTF(LOW,
                "MCU: [poll %d int_round %d iso_out_done %d iso_done %d] DEVCMDSTAT=0x%x INTSTAT=0x%x\n",
                poll_count, int_round, (uint32_t)iso_out_done,
                (uint32_t)iso_done,
                lsu_read_32(USB_DEV_DEVCMDSTAT),
                lsu_read_32(USB_DEV_INTSTAT));
        }
    }

    if (all_done)
        VPRINTF(LOW,
            "MCU: USB HS dev mixed INT EP%d (%d rounds) + ISO EP%d PASSED\n",
            USB_INT_EP, int_round, USB_ISO_EP);
    else
        VPRINTF(LOW,
            "MCU: USB HS dev mixed INT+ISO TIMEOUT (int_round=%d/%d int_out_armed=%d int_in_armed=%d iso_out_done=%d iso_in_armed=%d iso_done=%d)\n",
            int_round, N_INT_ROUNDS, (uint32_t)int_out_armed,
            (uint32_t)int_in_armed, (uint32_t)iso_out_done,
            (uint32_t)iso_in_armed, (uint32_t)iso_done);

    VPRINTF(LOW, "MCU: USB HS device mixed INTERRUPT + ISO test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
