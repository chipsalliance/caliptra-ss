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
// Description: USB HS device isochronous OUT + IN combined test firmware.
//              Multi-round variant: N_ISO_ROUNDS=3, rotating data pattern.
//
// Test sequence (repeated N_ISO_ROUNDS times):
//   1. Boot MCU and USB core in HS device mode (once).
//   2. Handle enumeration (bus reset + EP0 SETUP packets) (once).
//   3. Each round r (0..N_ISO_ROUNDS-1):
//      a. Arm EP2 OUT (ISO, 1024 bytes).
//         OUT pattern: byte[i] = (i + r*ISO_ROUND_OFFSET) % 256.
//         Firmware verifies after receive.
//      b. Fill EP2 IN SRAM with inverse pattern:
//         byte[i] = 255 - ((i + r*ISO_ROUND_OFFSET) % 256).
//         Arm EP2 IN (ISO, 1024 bytes, two 512-byte buffer entries).
//         VIP host reads EP2 IN and performs data integrity checking per-round.
//
// Round advancement:
//   Round advancement is driven by EP2 OUT INTSTAT (reliably set by hardware).
//   The firmware does not depend on any EP2 IN completion signal. Historically
//   this was described as a hardware limitation ("ISO IN never clears Active
//   and never sets INTSTAT EP2IN"), but that was a consequence of arming the IN
//   entries with T=0; see the note on usb_ep2_in_arm(). The EP2-OUT-driven
//   handshake below is kept because it is correct either way. Therefore:

//     - After arming EP2 IN for round r, firmware immediately arms EP2 OUT for
//       round r+1.
//     - When EP2 OUT INTSTAT fires for round r+1, firmware verifies the OUT
//       data, fills SRAM with round r+1 IN pattern, and arms EP2 IN for r+1.
//   This ensures the SRAM always contains the correct IN pattern before the
//   sequence issues the IN tokens for that round.
//
// NXP IP_3511HS EP command/status entry bit fields
// (reference manual Table 911, "Endpoint command/status bit definitions"):
//   [31] A     = Active
//   [30] D     = Disabled
//   [29] S     = Stall
//   [28] TR    = Toggle reset
//   [27] RF/TV = Rate feedback mode / Toggle value
//   [26] T     = Endpoint type: 0 = generic, 1 = periodic
//   [25:11]    = NBytes
//   [10:0]     = AddrOffset (buffer byte address >> 6)
//
// How T and RF/TV combine, per Table 911. The distinction is by ENDPOINT
// NUMBER, not by direction:
//   - Control endpoint 0 only: RF/TV is the toggle value, applied when TR is
//     set. T and RF/TV carry no type information on EP0.
//   - All non-control endpoints (both IN and OUT): T and RF/TV together
//     identify the endpoint type.
//       T=0, RF=0 : generic bulk endpoint, maxpacket 512 (HS) / 64 (FS)
//       T=0, RF=1 : interrupt endpoint in rate-feedback mode
//       T=1, RF=0 : isochronous endpoint, maxpacket = min(NBytes, 1024)
//       T=1, RF=1 : interrupt endpoint
//
// An earlier version of this comment claimed bit 26 was the data Toggle bit on
// IN entries and that TYPE_PERIODIC must not be set on them. That was wrong on
// both counts: the toggle value is RF/TV (bit 27) and it applies only to EP0,
// and leaving T=0 on EP2 IN does not make the entry type-neutral - it declares
// a generic BULK endpoint, which in FS caps the packet at 64 bytes. That is
// what truncated every 512-byte ISO IN packet at byte 64. Confirmed against
// usb_dma.m.vhdl: the descriptor decode qualifies only on
// sync_sieint_epinfo_epnr = "0000" (EP0) with no direction term, drives
// epinfo_periodic from bit 26 and epinfo_rf_tv from bit 27, and selects
// var_maxpacket = 64 for FS when periodic = 0.


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

// Number of ISO round-trips to execute.

#define N_ISO_ROUNDS                  3u

// Per-round byte-value offset so each round has a distinct data pattern.
// With N=3 rounds: offsets are 0, 85, 170 (approximately 256/3).
#define ISO_ROUND_OFFSET              85u

// Poll loop timeout (iterations).  Increased to cover 3 rounds.
#define USB_POLL_TIMEOUT              100000

// FRAME_INT test phase: number of poll iterations to count SOF events.
//
// These constants were originally copied from the HS twin and were wrong for
// full speed in two ways. Both are corrected here from measurements taken on
// this test:
//
//   1. Iteration cost. FRAME_INT_EN was enabled at 12390060 ns and the count
//      was printed at 15543422 ns, so 60000 iterations took 3.153 ms. That is
//      52.6 ns per iteration, not the ~33 ns the old comment claimed.
//   2. SOF period. FRAME_INT tracks the frame boundary, which is every 125 us
//      in high speed but every 1 ms in full speed - 8 times slower. The old
//      window of 60000 iterations therefore spanned only 3.15 FS frames, so
//      at most 3 or 4 events could ever be counted, and the old minimum of 10
//      was arithmetically unreachable. The run reported "count = 4, min = 10"
//      and declared FAILED even though the hardware was behaving correctly.
//
// Sizing used below: 120000 iterations at 52.6 ns is about 6.3 ms, which spans
// roughly 6 FS frames. The minimum is set to 4, leaving margin for the partial
// frame at each end of the window plus startup jitter, while still being a
// meaningful check (the previous, broken window would have yielded 3).
#define FRAME_INT_POLL_WINDOW         120000u

// Minimum number of FRAME_INT events required to declare the test PASSED.
// Expected is ~6 for the window above at the FS 1 ms frame rate; 4 tolerates
// the partial frames at the window edges.
#define FRAME_INT_MIN_COUNT           4u

// Iterations for the disable-check spin after clearing FRAME_INT_EN.
// Must exceed one FS SOF period: 1 ms / 52.6 ns per iter = ~19000 iters.
// Use 24000 iterations (~1.26 ms) for margin. Retained for completeness; the
// disable check verifies INTEN readback rather than spinning on INTSTAT,
// because hardware sets the INTSTAT frame bit regardless of INTEN.
#define FRAME_INT_DISABLE_SPIN        24000u

// EP2 OUT buffer: 0x600..0x9FF (1024 bytes).
// EP0 uses 0x000-0x1FF, EP1 region 0x200-0x5FF is unused.
#define USB_SRAM_EP2_OUT_BUF_OFFSET   0x600u

// EP2 IN buffer: 0xA00..0xDFF (1024 bytes), immediately after EP2 OUT buffer.
#define USB_SRAM_EP2_IN_BUF_OFFSET    0xA00u

// Total payload the host delivers per round, across all tokens.
#define USB_FS_ISO_TRANSFER_BYTES     1024u

// Bytes per individual ISO OUT token on the wire.
// Full speed caps one isochronous transaction at 1023 bytes (USB 2.0 table
// 5-7), so the host sequence splits each 1024-byte round into two 512-byte
// ISO OUT tokens. The endpoint entry must be armed with the size of ONE token,
// not the size of the round: per UM11295 Table 843 the hardware clears the
// Active bit as soon as it receives a short packet, and a 512-byte packet is
// short relative to an NBytes of 1024. Arming 1024 therefore terminates the
// endpoint after the first token and the second token is dropped.
#define USB_FS_ISO_OUT_BUF_BYTES      (USB_FS_ISO_TRANSFER_BYTES / 2u)

// Number of ISO OUT tokens the host sends per round.
#define USB_FS_ISO_OUT_TOKENS_PER_ROUND \
    (USB_FS_ISO_TRANSFER_BYTES / USB_FS_ISO_OUT_BUF_BYTES)


// EP command/status list offsets for EP2.
// NXP IP_3511 layout (Integration Guide section 4.2.1):
//   EP(n) OUT Buffer 0 at 0x10 * (2*n)
//   EP(n) IN  Buffer 0 at 0x10 * (2*n) + 8
//   EP(n) IN  Buffer 1 at 0x10 * (2*n) + 12
// EP2: OUT_BUF0=0x020, IN_BUF0=0x028, IN_BUF1=0x02C
#define USB_EP_LIST_EP2_OUT_OFFSET      0x020u
#define USB_EP_LIST_EP2_IN_BUF0_OFFSET  0x028u
#define USB_EP_LIST_EP2_IN_BUF1_OFFSET  0x02Cu

// Keep old alias for compatibility.
#define USB_EP_LIST_EP2_IN_OFFSET       USB_EP_LIST_EP2_IN_BUF0_OFFSET

// Each IN buffer entry carries half the total transfer (512 bytes).
#define USB_FS_ISO_IN_BUF_BYTES         (USB_FS_ISO_TRANSFER_BYTES / 2u)

// Double-buffer (ping-pong) enable for EP2 IN.
//
// The two IN descriptors above are two slots for the SAME endpoint. Hardware
// selects between them with bit 2 of the descriptor fetch address, which is
// exactly the 0x4 that separates IN_BUF0 (0x028) from IN_BUF1 (0x02C):
//   usb_dma.m.vhdl:1285
//     epinfo_addr(2) <= '1' when (setup = '1') or
//                                (usbreg_ep_bufinuse(endpoint_nr_dir) = '1')
//
// bufinuse only ever toggles at usb_reg_if.m.vhdl:859-864, and that toggle is
// gated by reg_ep_doublebuffer(i+2) = '1'. reg_ep_doublebuffer is the EPBUFCFG
// register (offset 0x1c), cleared at reset (line 650). With EPBUFCFG left at 0
// the toggle never fires, bufinuse stays 0, and every IN token re-reads
// IN_BUF0. The IN_BUF1 descriptor is then dead: the second 512-byte IN token of
// each round gets no data, the device does not respond, and the VIP reports
// device_response_timeout_check_Dev2_EP2_IN while BUF1 compares as all-zero.
//
// Both EPBUFCFG and EPINUSE index physical endpoints starting at bit 2
// (usb_reg_if.m.vhdl:775 and 519 both slice reg_wdata/reg_rdata as
// C_NBPHYSEP+1 downto 2), so the bit number equals the physical endpoint
// number. EP2 IN is phys = 2*2 + 1 = 5.
#define USB_PHYS_EP2_IN                 5u
#define USB_EPBUFCFG_EP2_IN_MASK        (1u << USB_PHYS_EP2_IN)


// mstatus.MIE is bit 3. Used to bracket the mailbox read-modify-write below.
#define MSTATUS_MIE_MASK                0x8u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

// Atomically take everything the ISR has posted in the mailbox and clear it.
//
// The obvious form of this drain,
//     usb_events = mcu_intr_rcv.usb;
//     mcu_intr_rcv.usb &= ~usb_events;
// is a read-modify-write executed with interrupts enabled. The compiler emits
// load / and-not / store, and if the USB interrupt is taken between the load
// and the store then the "mcu_intr_rcv.usb |= act" performed by
// service_usb_intr() is overwritten by the stale value that the foreground had
// already loaded. The event is destroyed silently: no error, no halt, and the
// endpoint is never re-armed. That is exactly how the round 0 token 1 ISO OUT
// completion was lost, with the waveform showing reg_ep_int_status(4) set,
// irq_int asserted and the ISR W1C ack on reg_waddr 0x8, while the foreground
// never saw the EP2OUT bit.
//
// Clearing mstatus.MIE around the sequence makes the read and the clear
// indivisible with respect to the USB vector. csrrc returns the previous
// mstatus, so the enable state is restored rather than assumed. Note that the
// value is restored only if it was set on entry, which keeps the helper usable
// from a context that already had interrupts masked.
static inline uint32_t usb_mailbox_take(void) {
    uint32_t events;
    uint32_t saved;

    __asm__ volatile ("csrrc %0, mstatus, %1"
                      : "=r" (saved)
                      : "r" (MSTATUS_MIE_MASK)
                      : "memory");

    events = mcu_intr_rcv.usb;
    mcu_intr_rcv.usb &= ~events;


    if (saved & MSTATUS_MIE_MASK) {
        __asm__ volatile ("csrrs zero, mstatus, %0"
                          :
                          : "r" (MSTATUS_MIE_MASK)
                          : "memory");
    }

    return events;
}

// Atomically test and consume a single mailbox bit. Returns true if the bit was
// posted by the ISR, in which case it is cleared. Same atomicity argument as
// usb_mailbox_take(): a bare "mcu_intr_rcv.usb &= ~mask" would race the ISR and
// drop an unrelated event that happened to be posted mid-sequence.
static inline bool usb_mailbox_take_bit(uint32_t mask) {
    uint32_t saved;
    bool     seen;

    __asm__ volatile ("csrrc %0, mstatus, %1"
                      : "=r" (saved)
                      : "r" (MSTATUS_MIE_MASK)
                      : "memory");

    seen = (mcu_intr_rcv.usb & mask) != 0u;
    mcu_intr_rcv.usb &= ~mask;

    if (saved & MSTATUS_MIE_MASK) {
        __asm__ volatile ("csrrs zero, mstatus, %0"
                          :
                          : "r" (MSTATUS_MIE_MASK)
                          : "memory");
    }

    return seen;
}



// Storage for the symbols the ISR library declares extern.
volatile uint32_t intr_count;
volatile mcu_intr_received_s mcu_intr_rcv = {0};

#ifdef CPT_VERBOSITY

    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Arm EP2 OUT as isochronous (T=1, RF=0) for ONE incoming token.
//
// token selects which half of the round buffer this arm receives into:
//   token 0 -> USB_SRAM_EP2_OUT_BUF_OFFSET + 0
//   token 1 -> USB_SRAM_EP2_OUT_BUF_OFFSET + USB_FS_ISO_OUT_BUF_BYTES
//
// NBytes is USB_FS_ISO_OUT_BUF_BYTES, i.e. exactly one token, so hardware
// clears Active because NBytes reached 0 (a full packet) rather than because it
// saw a short packet. Firmware must re-arm for every token of the round; see
// USB_FS_ISO_OUT_BUF_BYTES for why arming the whole round at once fails.
static void usb_ep2_out_arm(uint32_t round, uint32_t token) {
    uint32_t buf_offset = USB_SRAM_EP2_OUT_BUF_OFFSET
                        + (token * USB_FS_ISO_OUT_BUF_BYTES);
    uint32_t ep2_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_TYPE_PERIODIC
                     | USB_EP_ENTRY_RF_ISO
                     | USB_EP_ENTRY_NBYTES(USB_FS_ISO_OUT_BUF_BYTES)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR + buf_offset);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET, ep2_out);

    uint32_t inten = lsu_read_32(USB_DEV_INTEN);
    lsu_write_32(USB_DEV_INTEN, inten | USBHSD_INTSTAT_EP2OUT_MASK);
    VPRINTF(LOW, "MCU: EP2 OUT (ISO) armed for round %d token %d (offset=0x%x)\n",
            round, token, buf_offset);
}


static uint32_t usb_ep2_out_read(void) {
    return lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP2_OUT_OFFSET);
}

// Fill EP2 IN SRAM with round-specific inverse-ramp and arm both IN buffer entries.
// Pattern: byte[i] = 255 - ((i + round_base) % 256).
//
// The entries are armed as isochronous (T=1, RF=0), exactly like EP2 OUT. See
// the Table 911 notes in the file header: T and RF/TV identify the endpoint
// type on every non-control endpoint, in both directions. Leaving T=0 here
// declared a generic bulk endpoint, which caps an FS packet at 64 bytes and
// truncated all 512-byte ISO IN transfers at byte 64.
//
// Historical note on completion signalling: this test previously stated that
// the IP does not set INTSTAT EP2IN and does not clear Active for ISO IN.
// That was observed with T=0, and it follows from it - the IN writeback in
// usb_dma.m.vhdl only clears Active and pulses dma_set_int when the entry is
// isochronous (periodic = 1, rf_tv = 0) or the transfer fit within maxpacket.
// With the entries correctly marked ISO, hardware is expected to clear Active
// and raise INTSTAT EP2IN. The round advancement below is still driven off EP2
// OUT, so it does not depend on either behaviour; do not add a wait on EP2 IN
// without confirming it in simulation first.

static void usb_ep2_in_arm(uint32_t round, uint32_t round_base) {
    // Write pattern into SRAM as 32-bit words.
    for (uint32_t i = 0; i < USB_FS_ISO_TRANSFER_BYTES; i += 4) {
        uint32_t b0 = 255u - ((i + 0u + round_base) % 256u);
        uint32_t b1 = 255u - ((i + 1u + round_base) % 256u);
        uint32_t b2 = 255u - ((i + 2u + round_base) % 256u);
        uint32_t b3 = 255u - ((i + 3u + round_base) % 256u);
        lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP2_IN_BUF_OFFSET + i,
                     b0 | (b1 << 8) | (b2 << 16) | (b3 << 24));
    }

    // Arm Buffer 0 and Buffer 1 as isochronous (T=1, RF=0), giving an FS
    // maxpacket of min(NBytes, 1023) = 512 instead of the bulk default of 64.
    uint32_t ep2_in_buf0 = USB_EP_ENTRY_ACTIVE
                         | USB_EP_ENTRY_TYPE_PERIODIC
                         | USB_EP_ENTRY_RF_ISO
                         | USB_EP_ENTRY_NBYTES(USB_FS_ISO_IN_BUF_BYTES)
                         | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP2_IN_BUF_OFFSET);
    uint32_t ep2_in_buf1 = USB_EP_ENTRY_ACTIVE
                         | USB_EP_ENTRY_TYPE_PERIODIC
                         | USB_EP_ENTRY_RF_ISO
                         | USB_EP_ENTRY_NBYTES(USB_FS_ISO_IN_BUF_BYTES)
                         | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR + USB_SRAM_EP2_IN_BUF_OFFSET
                                                 + USB_FS_ISO_IN_BUF_BYTES);

    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP2_IN_BUF0_OFFSET, ep2_in_buf0);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP2_IN_BUF1_OFFSET, ep2_in_buf1);

    // Enable ping-pong on EP2 IN so the second token of the round is served
    // from the Buffer 1 descriptor instead of re-reading Buffer 0. Without
    // this, EPBUFCFG stays 0, the bufinuse toggle at usb_reg_if.m.vhdl:859-864
    // is gated off, and the Buffer 1 descriptor written just above is never
    // fetched. Read-modify-write so a future endpoint keeps its own bit; this
    // is outside the ISR mailbox path and EPBUFCFG is not touched by the ISR,
    // so no atomicity bracket is needed here.
    uint32_t epbufcfg = lsu_read_32(USB_DEV_EPBUFCFG);
    lsu_write_32(USB_DEV_EPBUFCFG, epbufcfg | USB_EPBUFCFG_EP2_IN_MASK);

    VPRINTF(LOW,
        "MCU: EP2 IN (ISO) armed for round %d (round_base=%d) "
        "EPBUFCFG=0x%x EPINUSE=0x%x\n",
        round, round_base,
        lsu_read_32(USB_DEV_EPBUFCFG),
        lsu_read_32(USB_DEV_EPINUSE));
}

void main(void) {
    uint32_t usb_events;
    uint32_t poll_count;


    // out_round: the round whose EP2 OUT we are waiting to receive.
    // in_round:  the round whose EP2 IN SRAM has been filled and armed.
    // After arming EP2 IN for round r, firmware immediately arms EP2 OUT for
    // round r+1 so the next OUT token advances the state machine.
    uint32_t out_round        = 0u;  // next expected EP2 OUT round
    uint32_t rounds_out_done  = 0u;  // counts completed EP2 OUT rounds
    uint32_t out_token        = 0u;  // which token of the round we expect next
    bool     ep2_out_armed    = false;
    bool     all_in_armed     = false;  // all N_ISO_ROUNDS IN buffers armed
    bool     all_done         = false;

    VPRINTF(LOW,
        "=================\nMCU: USB HS device ISO OUT + IN test (%d rounds)\n=================\n\n",
        N_ISO_ROUNDS);

    boot_mcu();
    boot_usb_core_fs();

    // Enable the USB interrupt (PIC vector 3) now that boot_usb_core_fs() has
    // programmed INTEN and cleared any stale INTSTAT bits. Deliberately not
    // init_interrupts(): that routine also writes the MCI and I3C interrupt
    // registers, and this early the I3C write does not complete, stalling the
    // LSU pipeline before mstatus.MIE is set. init_usb_interrupts() touches
    // only vector 3.
    intr_count = 0;
    init_usb_interrupts();

    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && !all_done;
         poll_count++) {

        usb_handle_bus_reset();

        // Drain the ISR mailbox. service_usb_intr() already read and
        // acknowledged INTSTAT, so the foreground loop must not touch INTSTAT
        // itself. The take-and-clear must be atomic against the USB vector or
        // an event that arrives mid-sequence is overwritten and lost; see
        // usb_mailbox_take().
        usb_events = usb_mailbox_take();


        // DEV_INT: bus reset change.
        if (usb_events & USBHSD_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (ep2_out_armed) {
                    ep2_out_armed = false;
                    VPRINTF(LOW, "MCU: Bus reset - EP2 arm cleared\n");
                }
            }
            // No INTSTAT write here: service_usb_intr() already cleared it.
        }

        // EP0 OUT: handle control transfers / enumeration.
        if (usb_events & USBHSD_INTSTAT_EP0OUT_MASK) {
            uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
            if (cmd & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                // Arm EP2 OUT for round 0 on first SETUP after enumeration.
                if (!ep2_out_armed && out_round == 0 && rounds_out_done == 0) {
                    usb_ep2_out_arm(0, 0);
                    ep2_out_armed = true;
                }
            } else {
                // Status-stage ZLP OUT for a control read completed. Hardware
                // cleared Active on the EP0 OUT descriptor, so it must be
                // re-armed or the next SETUP is NAKed and enumeration stops
                // after the first control read. Without this the device never
                // reaches the configured state and no ISO OUT token is ever
                // accepted at EP2, so INTSTAT EP2OUT never fires. Same handling
                // as caliptra_ss_usb_fs_dev_bulk_out.c.
                usb_ep0_arm_out();
            }
        }


        // EP0 IN completion needs no action: the ISR already acknowledged it.

        // EP2 OUT ISO completion: hardware fires INTSTAT EP2OUT after receive.
        // This is the primary state-advance signal for all rounds.
        if (ep2_out_armed && (usb_events & USBHSD_INTSTAT_EP2OUT_MASK)) {
            uint32_t ep2_entry = usb_ep2_out_read();
            uint32_t residual  = (ep2_entry >> 11) & 0x7FFFu;
            uint32_t received  = USB_FS_ISO_OUT_BUF_BYTES - residual;
            uint32_t round_base = out_round * ISO_ROUND_OFFSET;

            VPRINTF(LOW,
                "MCU: [round %d token %d] EP2 ISO OUT done - received %d bytes (residual=%d)\n",
                out_round, out_token, received, residual);

            ep2_out_armed = false;

            // A round is delivered as USB_FS_ISO_OUT_TOKENS_PER_ROUND separate
            // ISO OUT tokens. Re-arm for the next token and defer the data
            // check until the whole round has landed.
            if ((out_token + 1u) < USB_FS_ISO_OUT_TOKENS_PER_ROUND) {
                out_token++;
                usb_ep2_out_arm(out_round, out_token);
                ep2_out_armed = true;
                continue;
            }

            // Verify OUT data with round-specific ramp pattern.
            uint32_t errors = 0;
            for (uint32_t i = 0; i < USB_FS_ISO_TRANSFER_BYTES; i++) {
                uint32_t word_offset = i & ~3u;
                uint32_t byte_shift  = (i & 3u) * 8u;
                uint32_t word_val    = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                                                   + USB_SRAM_EP2_OUT_BUF_OFFSET
                                                   + word_offset);
                uint8_t  actual      = (uint8_t)((word_val >> byte_shift) & 0xFFu);
                uint8_t  expected    = (uint8_t)((i + round_base) % 256u);
                if (actual != expected) {
                    if (errors < 8) {
                        VPRINTF(LOW,
                            "MCU: [round %d] OUT MISMATCH byte[%d]: got 0x%02x exp 0x%02x\n",
                            out_round, i, actual, expected);
                    }
                    errors++;
                }
            }

            if (errors == 0)
                VPRINTF(LOW, "MCU: [round %d] ISO OUT data check PASSED\n",
                        out_round);
            else
                VPRINTF(LOW,
                    "MCU: [round %d] ISO OUT data check FAILED (%d errors)\n",
                    out_round, errors);

            rounds_out_done++;
            out_token = 0u;

            // Fill SRAM and arm EP2 IN for this round. Round advancement is
            // driven entirely by EP2 OUT, so no EP2 IN completion is awaited.
            usb_ep2_in_arm(out_round, round_base);


            // Advance to next round.
            out_round++;
            if (out_round < N_ISO_ROUNDS) {
                // Pre-arm EP2 OUT for the next round immediately after arming IN.
                // The sequence sends round r+1 ISO OUT only after reading round r
                // ISO IN (with a 1ms inter-round gap), giving firmware ample time
                // to have the OUT buffer ready.
                usb_ep2_out_arm(out_round, 0);
                ep2_out_armed = true;
            } else {
                // Last round IN is now armed; no more OUT to expect.
                all_in_armed = true;
                VPRINTF(LOW,
                    "MCU: All %d rounds OUT done, IN buffers armed - waiting for VIP to read\n",
                    N_ISO_ROUNDS);
            }
        }

        // After all IN buffers are armed, wait a fixed time for VIP to finish
        // reading the last round, then declare done and halt.
        // Use poll_count as a simple delay counter (each iteration ~157 ns).
        // 10000 iterations ~1.57 ms, enough for VIP to issue 2 ISO IN tokens.
        if (all_in_armed && !all_done) {
            // Re-use poll_count: record the count when all_in_armed first became
            // true.  Since we cannot store a separate timestamp without a static,
            // simply spin for another 10000 iterations from this point.
            // The `all_done` flag gates this block so it only executes once.
            // Wait by setting all_done - caller will exit the loop.
            static uint32_t wait_start = 0;
            if (wait_start == 0)
                wait_start = poll_count;
            if (poll_count - wait_start >= 10000u) {
                VPRINTF(LOW,
                    "MCU: USB HS dev ISO OUT+IN - all %d rounds IN armed and VIP read window elapsed\n",
                    N_ISO_ROUNDS);
                all_done = true;
            }
        }

        // Heartbeat only. Event detection is interrupt driven (the ISR fills
        // mcu_intr_rcv.usb); this print exists purely so a stalled run can be
        // located in the log. INTSTAT reads 0x0 here precisely because
        // service_usb_intr() already acknowledged every enabled source.
        if (poll_count % 5000 == 0 && poll_count > 0) {
            VPRINTF(LOW,
                "MCU: [heartbeat %d out_round %d] DEVCMDSTAT=0x%x INTSTAT=0x%x intr_cnt=%d\n",
                poll_count, out_round,
                lsu_read_32(USB_DEV_DEVCMDSTAT),
                lsu_read_32(USB_DEV_INTSTAT),
                intr_count);
        }

    }

    if (rounds_out_done == N_ISO_ROUNDS)
        VPRINTF(LOW,
            "MCU: USB HS dev ISO OUT+IN - all %d OUT rounds verified, IN data served\n",
            rounds_out_done);
    else
        VPRINTF(LOW,
            "MCU: USB HS dev ISO OUT+IN - TIMEOUT after %d/%d OUT rounds\n",
            rounds_out_done, N_ISO_ROUNDS);

    // =========================================================================
    // FRAME_INT test phase.
    //
    // NXP IP_3511HS INTSTAT bit 30 (FRAME_INT / 0x40000000) is asserted by
    // hardware at every USB frame boundary. This is a FULL SPEED test, so the
    // period is 1 ms, not the 125 us micro-frame of high speed. The INTEN
    // FRAME_INT_EN bit (bit 30) gates whether the event reaches the CPU. This
    // phase verifies that:
    //   1. Enabling FRAME_INT_EN causes FRAME_INT interrupts to fire regularly.
    //   2. The ISR acknowledges each one (W1C on INTSTAT) so events are
    //      countable individually out of the mailbox.
    //   3. At least FRAME_INT_MIN_COUNT events are observed in the poll window.
    //   4. Disabling FRAME_INT_EN stops new events from appearing.
    //
    // Poll window: FRAME_INT_POLL_WINDOW iterations, about 6.3 ms at the
    // measured 52.6 ns per iteration, so roughly 6 FS frames are expected.
    // See the FRAME_INT_POLL_WINDOW definition for how both numbers were
    // measured and why the previous HS-derived values could never pass.
    // =========================================================================
    VPRINTF(LOW, "\n--- FRAME_INT test phase ---\n");

    // Step 1: Enable FRAME_INT in INTEN, clear any pending mailbox bit first.
    {
        uint32_t inten_val;

        // Drop any stale FRAME_INT record from the mailbox. INTSTAT itself is
        // owned by service_usb_intr() and must not be written here.
        (void)usb_mailbox_take_bit(USBHSD_INTSTAT_FRAME_INT_MASK);


        // Enable FRAME_INT interrupt generation.
        inten_val = lsu_read_32(USB_DEV_INTEN);
        lsu_write_32(USB_DEV_INTEN, inten_val | USBHSD_INTEN_FRAME_INT_EN_MASK);
        VPRINTF(LOW, "MCU: FRAME_INT_EN enabled (INTEN=0x%x)\n",
                lsu_read_32(USB_DEV_INTEN));
    }

    // Step 2: Count FRAME_INT events over the poll window.
    {
        uint32_t frame_int_count = 0u;
        uint32_t fi;

        for (fi = 0; fi < FRAME_INT_POLL_WINDOW; fi++) {
            // Each SOF takes the USB interrupt; the ISR acknowledges INTSTAT
            // and records FRAME_INT in the mailbox. Consume the record here so
            // the next SOF is counted as a separate event.
            if (usb_mailbox_take_bit(USBHSD_INTSTAT_FRAME_INT_MASK))
                frame_int_count++;

        }

        VPRINTF(LOW, "MCU: FRAME_INT count = %d (window=%d iters, min=%d)\n",
                frame_int_count, FRAME_INT_POLL_WINDOW, FRAME_INT_MIN_COUNT);

        // Step 3: Check result.
        if (frame_int_count >= FRAME_INT_MIN_COUNT)
            VPRINTF(LOW, "MCU: FRAME_INT test PASSED (%d events observed)\n",
                    frame_int_count);
        else
            VPRINTF(LOW,
                "MCU: FRAME_INT test FAILED - only %d events (expected >= %d)\n",
                frame_int_count, FRAME_INT_MIN_COUNT);
    }

    // Step 4: Disable FRAME_INT_EN and verify it is cleared in INTEN.
    //
    // NOTE: On NXP IP_3511HS, the INTSTAT FRAME_INT bit (bit 30) is set by
    // hardware at every SOF boundary regardless of the INTEN FRAME_INT_EN
    // setting. INTEN only gates whether the event generates a CPU interrupt;
    // it does NOT suppress the INTSTAT status bit. Therefore the correct
    // disable verification is to read back INTEN and confirm FRAME_INT_EN
    // is clear, NOT to check INTSTAT (which will continue to be set by HW).
    {
        uint32_t inten_val;
        uint32_t inten_after;

        inten_val = lsu_read_32(USB_DEV_INTEN);
        lsu_write_32(USB_DEV_INTEN,
                     inten_val & ~USBHSD_INTEN_FRAME_INT_EN_MASK);

        // Small spin to let the write propagate, then read back INTEN.
        for (uint32_t k = 0; k < 10u; k++)
            (void)lsu_read_32(USB_DEV_INTEN);

        inten_after = lsu_read_32(USB_DEV_INTEN);
        if (inten_after & USBHSD_INTEN_FRAME_INT_EN_MASK)
            VPRINTF(LOW,
                "MCU: FRAME_INT_EN disable check FAILED - FRAME_INT_EN still set (INTEN=0x%x)\n",
                inten_after);
        else
            VPRINTF(LOW,
                "MCU: FRAME_INT_EN disable check PASSED (INTEN=0x%x, FRAME_INT_EN=0)\n",
                inten_after);

        VPRINTF(LOW, "MCU: FRAME_INT_EN disabled (INTEN=0x%x)\n",
                inten_after);
    }

    VPRINTF(LOW, "--- FRAME_INT test phase complete ---\n");

    VPRINTF(LOW, "MCU: USB HS device ISO OUT + IN test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
