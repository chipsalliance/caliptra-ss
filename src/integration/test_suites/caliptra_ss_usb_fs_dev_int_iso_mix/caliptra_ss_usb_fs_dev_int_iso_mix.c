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
// Description: USB FS device mixed INTERRUPT (EP1) + ISOCHRONOUS (EP2) +
//              INTERRUPT (EP3) test firmware. Full-speed counterpart of
//              caliptra_ss_usb_hs_dev_int_iso_mix.c, with the endpoint types
//              pinned to distinct logical endpoints so all three stay armed at
//              the same time and share the device DMA / EP command-status list.
//
// Host-side endpoint access order driven by
// caliptra_ss_usb_fs_dev_int_iso_mix_sequence: a SINGLE loop of EP1 -> EP2 ->
// EP3 (the HS twin runs two loops; one loop is used at FS because the frame
// period is 1 ms instead of 125 us, so each transaction costs roughly eight
// times more simulation time).
//   phase 0: EP1 INTERRUPT  (OUT 64 B then IN 64 B loopback), pattern base 0
//   phase 1: EP2 ISOCHRONOUS (OUT 2 x 512 B then 2 x IN 512 B)
//   phase 2: EP3 INTERRUPT  (OUT 64 B then IN 64 B loopback), pattern base 85
//
// The firmware itself is phase-agnostic: it arms EP1 OUT, EP3 OUT and EP2 OUT
// once the device address has been programmed and then services whichever
// endpoint the host decides to drive next. With N_LOOPS = 1 there is no
// per-loop pattern shift, so the expected byte values are simply
// (i + pattern_base) % 256 on the INTERRUPT endpoints and i % 256 on ISO OUT.
//
// Event model: POLLED, exactly like the HS mix test. INTSTAT is read and
// write-1-cleared by this loop, and no ISR / mailbox is used. Do not mix in
// the init_usb_interrupts() + usb_mailbox_take() model of
// caliptra_ss_usb_fs_dev_iso_out.c: the two are mutually exclusive, because
// service_usb_intr() acknowledges INTSTAT before the foreground can see it.
//
// Resource split (no overlap between the three endpoints):
//   resource            EP1 (INTERRUPT)  EP2 (ISOCHRONOUS)  EP3 (INTERRUPT)
//   EP-list OUT word    0x010            0x020              0x030
//   EP-list IN buf0     0x018            0x028              0x038
//   EP-list IN buf1     -                0x02C              -
//   SRAM OUT buffer     0x200 (64 B)     0x600 (1024 B)     0x240 (64 B)
//   SRAM IN  buffer     0x400 (64 B)     0xA00 (1024 B)     0x440 (64 B)
// EP0 keeps 0x000-0x1FF of the data region; the EP command/status list itself
// lives at offset 0 and must stay below the SETUP buffer at 0x100.
//
// NXP IP_3511HS EP command/status entry bit fields (UM11295 Table 911):
//   [31] A     = Active
//   [30] D     = Disabled
//   [29] S     = Stall
//   [28] TR    = Toggle reset
//   [27] RF/TV = Rate feedback mode / Toggle value
//   [26] T     = Endpoint type: 0 = generic, 1 = periodic
//   [25:11]    = NBytes
//   [10:0]     = AddrOffset (buffer byte address >> 6)
// On every non-control endpoint, in BOTH directions, T and RF/TV together
// identify the type:
//   T=0, RF=0 : generic bulk endpoint, maxpacket 512 (HS) / 64 (FS)
//   T=0, RF=1 : interrupt endpoint in rate-feedback mode
//   T=1, RF=0 : isochronous endpoint, maxpacket = min(NBytes, 1023 at FS)
//   T=1, RF=1 : interrupt endpoint
//
// Two FS-specific departures from the HS mix firmware, both of them required:
//   1. ISO IN entries are armed ACTIVE|TYPE_PERIODIC|RF_ISO (T=1, RF=0). The
//      HS firmware leaves T=0 on IN entries; at FS that declares a generic
//      BULK endpoint, which caps the packet at 64 bytes and truncates every
//      512-byte ISO IN at byte 64 (usb_dma.m.vhdl selects var_maxpacket = 64
//      for FS when periodic = 0).
//   2. ISO OUT is armed PER TOKEN with NBytes = 512, not once with 1024. Per
//      UM11295 Table 843 hardware clears Active as soon as it receives a short
//      packet, and a 512-byte packet is short relative to an NBytes of 1024,
//      so arming the whole round terminates the endpoint after the first token
//      and the second token is dropped.
// EP2 IN also needs the EPBUFCFG ping-pong bit set, see USB_EPBUFCFG_EP2_IN_MASK.
//
// Completion-signal asymmetry between the endpoint types:
//   INTERRUPT: the host ACKs, so hardware CLEARS the Active bit of the OUT and
//              IN entries. The INTSTAT bit index 2*n is not reliable for an
//              arbitrary endpoint, so the Active bit is the completion signal.
//   ISO OUT:   hardware sets INTSTAT EP2OUT on receive (reliable).
//   ISO IN:    round advancement here does not wait on any ISO IN completion;
//              the firmware only guarantees the SRAM payload is in place
//              before the host issues the IN tokens, then closes the phase
//              after a bounded read window.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Logical endpoint assignment. All are inside the compiled physical-endpoint
// set (phys = 2*epnr + epdir must be <= C_NBPHYSEP+1 = 15 for the default
// C_NBPHYSEP=14 this DUT instantiates), i.e. logical EP0..EP7 are usable.
#define USB_INT_EP                    1u
#define USB_ISO_EP                    2u
#define USB_INT_EP2                   3u

// Number of INTERRUPT endpoints serviced by the table below.
#define N_INT_EPS                     2u

// Byte-value offset applied on the second INTERRUPT endpoint so each interrupt
// endpoint carries a distinct pattern: byte[i] = (i + pattern_base) % 256.
// Must match INT_ROUND_OFFSET in the UVM sequence.
#define INT_ROUND_OFFSET              85u

// Number of EP1 -> EP2 -> EP3 loops the host drives. The FS sequence runs a
// single loop, so there is no per-loop pattern shift.
#define N_LOOPS                       1u

// Interrupt transfer size. 64 bytes is legal for both FS and HS interrupt
// endpoints (usb_dma.m.vhdl maxpacket encoding "00").
#define USB_INT_TRANSFER_BYTES        64u

// Total ISO payload the host delivers per round, across all tokens.
#define USB_FS_ISO_TRANSFER_BYTES     1024u

// Bytes per individual ISO token on the wire, in both directions. Full speed
// caps one isochronous transaction at 1023 bytes (USB 2.0 table 5-7), so the
// host sequence splits each 1024-byte round into two 512-byte tokens.
#define USB_FS_ISO_OUT_BUF_BYTES      (USB_FS_ISO_TRANSFER_BYTES / 2u)
#define USB_FS_ISO_IN_BUF_BYTES       (USB_FS_ISO_TRANSFER_BYTES / 2u)

// Number of ISO OUT tokens the host sends per round.
#define USB_FS_ISO_OUT_TOKENS_PER_ROUND \
    (USB_FS_ISO_TRANSFER_BYTES / USB_FS_ISO_OUT_BUF_BYTES)

// Poll loop timeout (iterations). At the measured 52.6 ns per iteration this
// is about 7.9 ms, which covers FS enumeration plus the single
// EP1 -> EP2 -> EP3 loop at the 1 ms FS frame rate, with margin.
#define USB_POLL_TIMEOUT              150000

// Iterations to keep spinning after the ISO IN buffers are armed so the host
// has a window to issue its two IN tokens. Round advancement does not depend
// on an ISO IN completion signal, so this bounded window is what closes the
// ISO phase. ~2000 iterations is ~105 us, which is ample once the payload is
// already in SRAM; the sequence itself spaces the two IN tokens 125 us apart
// and holds a long drain delay afterwards.
#define ISO_IN_READ_WINDOW            2000u

// Double-buffer (ping-pong) enable for EP2 IN.
//
// The two IN descriptors are two slots for the SAME endpoint. Hardware selects
// between them with bit 2 of the descriptor fetch address, which is exactly
// the 0x4 that separates IN_BUF0 from IN_BUF1. bufinuse only toggles when
// reg_ep_doublebuffer (the EPBUFCFG register) has the endpoint bit set, and
// EPBUFCFG is cleared at reset. With EPBUFCFG left at 0 the toggle never
// fires, bufinuse stays 0, every IN token re-reads BUF0, and the second
// 512-byte IN token of the round gets no data (the VIP then reports
// device_response_timeout_check_Dev2_EP2_IN while BUF1 compares as all-zero).
// EPBUFCFG indexes PHYSICAL endpoints starting at bit 2, so the bit number
// equals the physical endpoint number; EP2 IN is phys = 2*2 + 1 = 5.
#define USB_PHYS_EP2_IN               5u
#define USB_EPBUFCFG_EP2_IN_MASK      (1u << USB_PHYS_EP2_IN)

// EP command/status list offsets, derived from the endpoint number per
// Integration Guide 4.2.1. The list is a table of 16-byte (0x10) blocks
// indexed by LOGICAL endpoint:
//   EP(n) OUT      command/status word at 0x10*n
//   EP(n) IN buf0  command/status word at 0x10*n + 8
//   EP(n) IN buf1  command/status word at 0x10*n + 0xC
// Confirmed against usb_dma.m.vhdl, which builds the list address as
// epinfo_addr[7:4]=epnr, [3]=epdir, [2]=buffer select, [1:0]=0.
// Do NOT use a 0x10*(2*n) stride: arming at the wrong slot makes the DMA fetch
// an all-zero descriptor so the device NAKs every token.
#define USB_EP_LIST_OUT_OFFSET(n)     (0x10u * (n))
#define USB_EP_LIST_IN_BUF0_OFFSET(n) (0x10u * (n) + 8u)
#define USB_EP_LIST_IN_BUF1_OFFSET(n) (0x10u * (n) + 0xCu)

// Data buffers. EP0 owns 0x000-0x1FF. All offsets are 64-byte aligned because
// the entry AddrOffset field is the byte address >> 6.
#define USB_SRAM_INT_OUT_BUF_OFFSET   0x200u
#define USB_SRAM_INT_IN_BUF_OFFSET    0x400u
#define USB_SRAM_INT2_OUT_BUF_OFFSET  0x240u
#define USB_SRAM_INT2_IN_BUF_OFFSET   0x440u
#define USB_SRAM_ISO_OUT_BUF_OFFSET   0x600u
#define USB_SRAM_ISO_IN_BUF_OFFSET    0xA00u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// -------------------------------------------------------------------------
// INTERRUPT endpoint table (EP1 and EP3)
// -------------------------------------------------------------------------

// One entry per INTERRUPT endpoint. Each endpoint owns its own OUT/IN SRAM
// buffers and its own expected data pattern, so the whole OUT-verify ->
// copy -> arm-IN -> IN-complete flow is identical for both and is driven from
// this table instead of being duplicated per endpoint.
typedef struct {
    uint32_t ep_num;         // logical endpoint number
    uint32_t out_buf_offset; // SRAM offset of the OUT (receive) buffer
    uint32_t in_buf_offset;  // SRAM offset of the IN (loopback) buffer
    uint32_t pattern_base;   // byte[i] = (i + pattern_base) % 256
    uint32_t rounds_done;    // completed OUT+IN loopback rounds (0..N_LOOPS)
    bool     out_armed;      // OUT entry currently armed
    bool     in_armed;       // IN entry currently armed
    bool     done;           // all N_LOOPS rounds completed on this endpoint
} usb_int_ep_t;

static usb_int_ep_t int_eps[N_INT_EPS] = {
    { USB_INT_EP,  USB_SRAM_INT_OUT_BUF_OFFSET,  USB_SRAM_INT_IN_BUF_OFFSET,
      0u,                0u, false, false, false },
    { USB_INT_EP2, USB_SRAM_INT2_OUT_BUF_OFFSET, USB_SRAM_INT2_IN_BUF_OFFSET,
      INT_ROUND_OFFSET,  0u, false, false, false }
};

// Arm an INTERRUPT OUT entry (T=1, RF=1) and unmask its completion interrupt.
static void usb_int_ep_out_arm(const usb_int_ep_t *ep) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_TYPE_PERIODIC
                   | USB_EP_ENTRY_RF_INT
                   | USB_EP_ENTRY_NBYTES(USB_INT_TRANSFER_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + ep->out_buf_offset);
    uint32_t slot = USB_DEV_DMA_BASE_ADDR
                    + USB_EP_LIST_OUT_OFFSET(ep->ep_num);
    uint32_t inten;
    uint32_t rb;

    lsu_write_32(slot, entry);

    // INTSTAT/INTEN bit index for EP(n) OUT is 2*n (EP0 OUT = bit 0).
    inten = lsu_read_32(USB_DEV_INTEN);
    lsu_write_32(USB_DEV_INTEN, inten | (1u << (2u * ep->ep_num)));

    // Readback: if the slot address is wrong this reads back 0 instead of the
    // armed entry, which separates an addressing bug from a datapath issue.
    rb = lsu_read_32(slot);
    VPRINTF(LOW,
        "MCU: EP%d OUT armed as INTERRUPT (T=1,RF=1), %d bytes; "
        "slot=0x%x wrote=0x%x readback=0x%x%s\n",
        ep->ep_num, USB_INT_TRANSFER_BYTES, slot, entry, rb,
        (rb == entry) ? "" : " <<< MISMATCH");
}

// Arm an INTERRUPT IN entry (T=1, RF=1), same type encoding as the OUT entry:
// per Table 911 the type is identified by T and RF/TV on every non-control
// endpoint, in both directions.
static void usb_int_ep_in_arm(const usb_int_ep_t *ep) {
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_TYPE_PERIODIC
                   | USB_EP_ENTRY_RF_INT
                   | USB_EP_ENTRY_NBYTES(USB_INT_TRANSFER_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                           + ep->in_buf_offset);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                 + USB_EP_LIST_IN_BUF0_OFFSET(ep->ep_num), entry);

    VPRINTF(LOW, "MCU: EP%d IN armed with %d loopback bytes\n",
            ep->ep_num, USB_INT_TRANSFER_BYTES);
}

// -------------------------------------------------------------------------
// EP2 - ISOCHRONOUS
// -------------------------------------------------------------------------

// Arm EP2 OUT as isochronous (T=1, RF=0) for ONE incoming token.
//
// token selects which half of the round buffer this arm receives into:
//   token 0 -> USB_SRAM_ISO_OUT_BUF_OFFSET + 0
//   token 1 -> USB_SRAM_ISO_OUT_BUF_OFFSET + USB_FS_ISO_OUT_BUF_BYTES
//
// NBytes is one token, so hardware clears Active because NBytes reached 0 (a
// full packet) rather than because it saw a short packet. Firmware must re-arm
// for every token of the round; see USB_FS_ISO_OUT_BUF_BYTES for why arming
// the whole round at once fails at FS.
static void usb_iso_ep_out_arm(uint32_t token) {
    uint32_t buf_offset = USB_SRAM_ISO_OUT_BUF_OFFSET
                        + (token * USB_FS_ISO_OUT_BUF_BYTES);
    uint32_t entry = USB_EP_ENTRY_ACTIVE
                   | USB_EP_ENTRY_TYPE_PERIODIC
                   | USB_EP_ENTRY_RF_ISO
                   | USB_EP_ENTRY_NBYTES(USB_FS_ISO_OUT_BUF_BYTES)
                   | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR + buf_offset);
    uint32_t slot = USB_DEV_DMA_BASE_ADDR
                    + USB_EP_LIST_OUT_OFFSET(USB_ISO_EP);
    uint32_t inten;

    lsu_write_32(slot, entry);

    inten = lsu_read_32(USB_DEV_INTEN);
    lsu_write_32(USB_DEV_INTEN, inten | DEV0_CSR_INTSTAT_EP2OUT_MASK);

    VPRINTF(LOW,
        "MCU: EP%d OUT armed as ISO (T=1,RF=0) for token %d, %d bytes; "
        "slot=0x%x offset=0x%x entry=0x%x\n",
        USB_ISO_EP, token, USB_FS_ISO_OUT_BUF_BYTES, slot, buf_offset, entry);
}

static uint32_t usb_iso_ep_out_read(void) {
    return lsu_read_32(USB_DEV_DMA_BASE_ADDR
                       + USB_EP_LIST_OUT_OFFSET(USB_ISO_EP));
}

// Fill the EP2 IN SRAM with the inverse ramp byte[i] = 255 - (i % 256) and arm
// both IN buffer entries (512 bytes each) as isochronous (T=1, RF=0). The host
// checks this payload. Leaving T=0 here would declare a generic BULK endpoint,
// capping an FS packet at 64 bytes and truncating both 512-byte ISO IN tokens.
static void usb_iso_ep_in_arm(void) {
    uint32_t i;
    uint32_t buf0;
    uint32_t buf1;
    uint32_t epbufcfg;

    for (i = 0; i < USB_FS_ISO_TRANSFER_BYTES; i += 4) {
        uint32_t b0 = 255u - ((i + 0u) % 256u);
        uint32_t b1 = 255u - ((i + 1u) % 256u);
        uint32_t b2 = 255u - ((i + 2u) % 256u);
        uint32_t b3 = 255u - ((i + 3u) % 256u);
        lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_ISO_IN_BUF_OFFSET + i,
                     b0 | (b1 << 8) | (b2 << 16) | (b3 << 24));
    }

    buf0 = USB_EP_ENTRY_ACTIVE
         | USB_EP_ENTRY_TYPE_PERIODIC
         | USB_EP_ENTRY_RF_ISO
         | USB_EP_ENTRY_NBYTES(USB_FS_ISO_IN_BUF_BYTES)
         | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                 + USB_SRAM_ISO_IN_BUF_OFFSET);
    buf1 = USB_EP_ENTRY_ACTIVE
         | USB_EP_ENTRY_TYPE_PERIODIC
         | USB_EP_ENTRY_RF_ISO
         | USB_EP_ENTRY_NBYTES(USB_FS_ISO_IN_BUF_BYTES)
         | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                 + USB_SRAM_ISO_IN_BUF_OFFSET
                                 + USB_FS_ISO_IN_BUF_BYTES);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                 + USB_EP_LIST_IN_BUF0_OFFSET(USB_ISO_EP), buf0);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR
                 + USB_EP_LIST_IN_BUF1_OFFSET(USB_ISO_EP), buf1);

    // Enable ping-pong on EP2 IN so the second token of the round is served
    // from the BUF1 descriptor instead of re-reading BUF0. Read-modify-write
    // so a future endpoint keeps its own bit.
    epbufcfg = lsu_read_32(USB_DEV_EPBUFCFG);
    lsu_write_32(USB_DEV_EPBUFCFG, epbufcfg | USB_EPBUFCFG_EP2_IN_MASK);

    VPRINTF(LOW,
        "MCU: EP%d IN (ISO) armed - buf0=0x%x buf1=0x%x (%d bytes each) "
        "EPBUFCFG=0x%x EPINUSE=0x%x\n",
        USB_ISO_EP, buf0, buf1, USB_FS_ISO_IN_BUF_BYTES,
        lsu_read_32(USB_DEV_EPBUFCFG),
        lsu_read_32(USB_DEV_EPINUSE));
}

// -------------------------------------------------------------------------

void main(void) {
    uint32_t reg_data;
    uint32_t intstat;
    uint32_t poll_count;
    uint32_t i;
    uint32_t e;

    // INTERRUPT state lives in int_eps[] (one entry per interrupt endpoint).
    uint32_t int_done_cnt     = 0u;   // interrupt endpoints that finished

    // ISOCHRONOUS state.
    bool     iso_out_armed    = false;
    bool     iso_out_done     = false;
    bool     iso_in_armed     = false;
    bool     iso_done         = false;
    uint32_t iso_out_token    = 0u;   // which token of the round is expected
    uint32_t iso_wait_start   = 0u;
    uint32_t iso_rounds_done  = 0u;   // completed ISO OUT + IN rounds

    bool     all_done         = false;

    // Boundary guard: the EP command/status list is a contiguous table at
    // offset 0 indexed by logical endpoint. The highest slot used here (EP3 IN
    // buf0 at 0x038) must end at or before the SETUP buffer at 0x100 so the
    // list does not overrun EP0's control/data buffers.
    if ((USB_EP_LIST_OUT_OFFSET(USB_INT_EP2) + 0x10u)
        > USB_SRAM_SETUP_BUF_OFFSET) {
        VPRINTF(FATAL,
            "MCU: EP%d list slot 0x%x overruns SETUP buffer 0x%x - aborting\n",
            USB_INT_EP2, USB_EP_LIST_OUT_OFFSET(USB_INT_EP2),
            USB_SRAM_SETUP_BUF_OFFSET);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
        while (1);
    }

    VPRINTF(LOW,
        "=================\nMCU: USB FS device mixed INTERRUPT EP%d + ISO EP%d + INTERRUPT EP%d test\n=================\n\n",
        USB_INT_EP, USB_ISO_EP, USB_INT_EP2);

    boot_mcu();
    boot_usb_core_fs();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !all_done;
         poll_count++) {

        // Any bus reset clears the Active bit on ALL endpoints and
        // usb_handle_bus_reset() only restores EP0, so every data endpoint must
        // be re-armed explicitly whenever DRES_C was observed.
        uint32_t prev_dres = lsu_read_32(USB_DEV_DEVCMDSTAT)
                             & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK;
        usb_handle_bus_reset();
        if (prev_dres) {
            for (e = 0; e < N_INT_EPS; e++) {
                if (int_eps[e].out_armed && !int_eps[e].in_armed
                    && !int_eps[e].done) {
                    VPRINTF(LOW, "MCU: Bus reset - re-arming EP%d OUT\n",
                            int_eps[e].ep_num);
                    usb_int_ep_out_arm(&int_eps[e]);
                }
            }
            if (iso_out_armed && !iso_out_done) {
                VPRINTF(LOW, "MCU: Bus reset - re-arming EP%d OUT token %d\n",
                        USB_ISO_EP, iso_out_token);
                usb_iso_ep_out_arm(iso_out_token);
            }
        }

        reg_data = lsu_read_32(USB_DEV_DEVCMDSTAT);
        intstat  = lsu_read_32(USB_DEV_INTSTAT);

        // EP0 OUT: enumeration / control transfers.
        if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
            } else {
                // Status-stage ZLP OUT for a control read completed. Hardware
                // cleared Active on the EP0 OUT descriptor, so it must be
                // re-armed or the next SETUP is NAKed and enumeration stops
                // after the first control read. This matters at FS, where the
                // control reads of enumeration are what bring the device to
                // the configured state.
                usb_ep0_arm_out();
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
        if ((lsu_read_32(USB_DEV_DEVCMDSTAT)
             & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK) != 0u) {
            for (e = 0; e < N_INT_EPS; e++) {
                if (!int_eps[e].out_armed) {
                    usb_int_ep_out_arm(&int_eps[e]);
                    int_eps[e].out_armed = true;
                }
            }
            if (!iso_out_armed) {
                usb_iso_ep_out_arm(iso_out_token);
                iso_out_armed = true;
            }
        }

        // EP0 IN: status-phase completion.
        if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK)
            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);

        // ---------------------------------------------------------------
        // INTERRUPT state machine, run for every interrupt endpoint in the
        // table (EP1 and EP3). Both endpoints stay armed for the whole run,
        // so the host is free to drive them in any order; this firmware
        // simply reacts to whichever one completes.
        // ---------------------------------------------------------------
        for (e = 0; e < N_INT_EPS; e++) {
            usb_int_ep_t *ep       = &int_eps[e];
            uint32_t      ep_mask  = (1u << (2u * ep->ep_num));

            // INTERRUPT OUT completion: detected by hardware CLEARING the
            // Active bit of the OUT entry (the INTSTAT bit index is not
            // reliable for an arbitrary endpoint). The INTSTAT bit is still
            // write-1-cleared opportunistically so the status register does
            // not latch up.
            if (ep->out_armed && !ep->in_armed && !ep->done) {
                uint32_t entry = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                     + USB_EP_LIST_OUT_OFFSET(ep->ep_num));

                if (!(entry & USB_EP_ENTRY_ACTIVE)) {
                    uint32_t residual;
                    uint32_t errors = 0u;

                    if (intstat & ep_mask)
                        lsu_write_32(USB_DEV_INTSTAT, ep_mask);

                    residual = (entry >> 11) & 0x7FFFu;

                    VPRINTF(LOW,
                        "MCU: EP%d INTERRUPT OUT done - received %d bytes (residual=%d)\n",
                        ep->ep_num,
                        USB_INT_TRANSFER_BYTES - residual, residual);

                    // Expected host pattern: byte[i] = (i + base) % 256.
                    for (i = 0; i < USB_INT_TRANSFER_BYTES; i++) {
                        uint32_t word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                                    + ep->out_buf_offset
                                                    + (i & ~3u));
                        uint8_t  actual   = (uint8_t)((word >> ((i & 3u) * 8u))
                                                      & 0xFFu);
                        uint8_t  expected =
                            (uint8_t)((i + ep->pattern_base) % 256u);
                        if (actual != expected) {
                            if (errors < 8)
                                VPRINTF(LOW,
                                    "MCU: EP%d OUT MISMATCH byte[%d]: got 0x%x exp 0x%x\n",
                                    ep->ep_num, i, actual, expected);
                            errors++;
                        }
                    }
                    if (errors == 0)
                        VPRINTF(LOW,
                            "MCU: EP%d INTERRUPT OUT data check PASSED\n",
                            ep->ep_num);
                    else
                        VPRINTF(LOW,
                            "MCU: EP%d INTERRUPT OUT data check FAILED (%d errors)\n",
                            ep->ep_num, errors);

                    // Copy the received payload into the IN buffer and arm IN.
                    for (i = 0; i < USB_INT_TRANSFER_BYTES; i += 4) {
                        uint32_t word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                                    + ep->out_buf_offset + i);
                        lsu_write_32(USB_DEV_DMA_BASE_ADDR
                                     + ep->in_buf_offset + i, word);
                    }
                    usb_int_ep_in_arm(ep);
                    ep->in_armed = true;
                }
            }

            // INTERRUPT IN completion: unlike isochronous IN, an interrupt IN
            // is ACKed by the host, so hardware does clear the Active bit.
            if (ep->in_armed) {
                uint32_t in_entry = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                 + USB_EP_LIST_IN_BUF0_OFFSET(ep->ep_num));
                if (!(in_entry & USB_EP_ENTRY_ACTIVE)) {
                    ep->in_armed = false;
                    ep->rounds_done++;

                    VPRINTF(LOW,
                        "MCU: EP%d INTERRUPT loopback round %d/%d PASSED\n",
                        ep->ep_num, ep->rounds_done, N_LOOPS);

                    if (ep->rounds_done < N_LOOPS) {
                        usb_int_ep_out_arm(ep);
                        ep->out_armed = true;
                    } else {
                        ep->done = true;
                        int_done_cnt++;
                        VPRINTF(LOW,
                            "MCU: EP%d INTERRUPT all %d rounds done (%d/%d interrupt endpoints complete)\n",
                            ep->ep_num, N_LOOPS, int_done_cnt, N_INT_EPS);
                    }
                }
            }
        }

        // ---------------------------------------------------------------
        // EP2 ISOCHRONOUS state machine.
        // ---------------------------------------------------------------

        // ISO OUT completion: hardware reliably sets INTSTAT EP2OUT. A round
        // arrives as USB_FS_ISO_OUT_TOKENS_PER_ROUND separate 512-byte tokens,
        // so the entry is re-armed per token and the data check is deferred
        // until the whole round has landed.
        if (iso_out_armed && !iso_out_done
            && (intstat & DEV0_CSR_INTSTAT_EP2OUT_MASK)) {
            uint32_t iso_entry;
            uint32_t residual;

            lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP2OUT_MASK);

            iso_entry = usb_iso_ep_out_read();
            residual  = (iso_entry >> 11) & 0x7FFFu;

            VPRINTF(LOW,
                "MCU: EP%d ISO OUT token %d done - received %d bytes (residual=%d)\n",
                USB_ISO_EP, iso_out_token,
                USB_FS_ISO_OUT_BUF_BYTES - residual, residual);

            iso_out_armed = false;

            if ((iso_out_token + 1u) < USB_FS_ISO_OUT_TOKENS_PER_ROUND) {
                iso_out_token++;
                usb_iso_ep_out_arm(iso_out_token);
                iso_out_armed = true;
            } else {
                uint32_t errors = 0u;

                iso_out_token = 0u;

                // Expected host pattern across the whole round:
                // byte[i] = i % 256.
                for (i = 0; i < USB_FS_ISO_TRANSFER_BYTES; i++) {
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

                // Fill SRAM and arm EP2 IN. Round advancement does not wait on
                // an ISO IN completion, so this is the last action the firmware
                // can take for the ISO phase.
                usb_iso_ep_in_arm();
                iso_in_armed   = true;
                iso_wait_start = poll_count;
            }
        }

        // Once the IN buffers are armed, give the host a bounded window to
        // issue its two IN tokens. When the window elapses the round is
        // considered served.
        if (iso_in_armed && !iso_done
            && (poll_count - iso_wait_start) >= ISO_IN_READ_WINDOW) {
            iso_rounds_done++;
            VPRINTF(LOW,
                "MCU: EP%d ISO IN read window elapsed - round %d/%d complete\n",
                USB_ISO_EP, iso_rounds_done, N_LOOPS);

            if (iso_rounds_done < N_LOOPS) {
                iso_out_done = false;
                iso_in_armed = false;
                usb_iso_ep_out_arm(iso_out_token);
                iso_out_armed = true;
            } else {
                iso_done = true;
            }
        }

        // Every endpoint family finished.
        if (int_done_cnt >= N_INT_EPS && iso_done)
            all_done = true;

        if (poll_count % 5000 == 0 && poll_count > 0) {
            VPRINTF(LOW,
                "MCU: [poll %d int_done %d int_rounds %d/%d iso_rounds %d/%d iso_token %d iso_out_done %d iso_done %d] DEVCMDSTAT=0x%x INTSTAT=0x%x\n",
                poll_count, int_done_cnt,
                int_eps[0].rounds_done, int_eps[1].rounds_done,
                iso_rounds_done, N_LOOPS, iso_out_token,
                (uint32_t)iso_out_done, (uint32_t)iso_done,
                lsu_read_32(USB_DEV_DEVCMDSTAT),
                lsu_read_32(USB_DEV_INTSTAT));
        }
    }

    if (all_done)
        VPRINTF(LOW,
            "MCU: USB FS dev mixed INT EP%d + ISO EP%d + INT EP%d PASSED (%d loop of EP%d -> EP%d -> EP%d)\n",
            USB_INT_EP, USB_ISO_EP, USB_INT_EP2, N_LOOPS,
            USB_INT_EP, USB_ISO_EP, USB_INT_EP2);
    else
        VPRINTF(LOW,
            "MCU: USB FS dev mixed INT+ISO TIMEOUT (loops=%d int_done=%d/%d ep%d[rounds=%d out=%d in=%d done=%d] ep%d[rounds=%d out=%d in=%d done=%d] iso_rounds=%d iso_token=%d iso_out_done=%d iso_in_armed=%d iso_done=%d)\n",
            N_LOOPS, int_done_cnt, N_INT_EPS,
            int_eps[0].ep_num, int_eps[0].rounds_done,
            (uint32_t)int_eps[0].out_armed,
            (uint32_t)int_eps[0].in_armed, (uint32_t)int_eps[0].done,
            int_eps[1].ep_num, int_eps[1].rounds_done,
            (uint32_t)int_eps[1].out_armed,
            (uint32_t)int_eps[1].in_armed, (uint32_t)int_eps[1].done,
            iso_rounds_done, iso_out_token,
            (uint32_t)iso_out_done, (uint32_t)iso_in_armed,
            (uint32_t)iso_done);

    VPRINTF(LOW, "MCU: USB FS device mixed INTERRUPT + ISO test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
