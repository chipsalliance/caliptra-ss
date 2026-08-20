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
// Description: USB HS device endpoint SKIP test firmware for the Caliptra SS.
//
// EPSKIP (SOC_USBHSD_EPSKIP, offset 0x14) is the only legal way for firmware
// to take back ownership of an endpoint buffer it has already armed. Once the
// Active bit of an endpoint command/status entry is set, the entry belongs to
// hardware and firmware may not modify it (USB Integration Guide 4.2.3 "A"
// bit, 4.2.2.6, 4.2.4.2.1).
//
// Hardware behaviour (usb_dma.m.vhdl / usb_reg_if.m.vhdl):
//   - The DMA engine round-robin scans every skip bit while it sits in IDLE.
//     The scan is free running and needs no USB bus traffic.
//   - On a set bit it enters READ_EPINFO_SKIP, fetches the endpoint entry at
//     EPLISTSTART + phys_ep*8 + (EPINUSE[phys_ep] ? 4 : 0), forces Active to
//     zero, writes the word back (WAIT_ON_GNT_FOR_SKIP_UPDATE) and asserts
//     dma_clear_skip.
//   - dma_clear_skip self-clears EPSKIP[phys_ep] and, only when the fetched
//     Active bit was 1, sets INTSTAT[phys_ep].
//   - EPINUSE is deliberately NOT toggled by a skip.
//
// Physical endpoint numbering / EP command status list offsets:
//   phys 0 = EP0 OUT (0x000, SETUP entry at 0x004)
//   phys 1 = EP0 IN  (0x008)
//   phys 2 = EP1 OUT (0x010)
//   phys 3 = EP1 IN  (0x018)
//
// Test phases (run after the VIP host has finished enumeration):
//   E : skip EP1 IN while Active = 0     -> bit self-clears, NO interrupt
//   A : skip an idle armed EP1 OUT       -> Active cleared, residual intact,
//                                           INTSTAT.EP1OUT set, EPINUSE intact
//   D : skip an armed EP1 IN never polled -> Active cleared, INTSTAT.EP1IN set
//   B : skip EP1 OUT mid transfer (host sent 512 of the 2048 armed bytes)
//                                        -> residual 1536, data pattern ok
//   C : re-arm EP1 OUT and complete a normal 512 byte transfer
//                                        -> proves the endpoint recovers
//
// USB SRAM map used by this test (DATABUFSTART = 0):
//   0x000-0x1FF  EP command/status list + EP0 buffers (see usb.h / usb.c)
//   0x200-0x3FF  EP1 OUT phase B buffer (2048 armed, 512 actually received)
//   0x400-0x5FF  EP1 OUT phase C buffer (512 bytes)
//   0x600-0x63F  EP1 IN  phase D buffer (64 bytes, never transmitted)

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Main event loop bound. HS chirp alone takes ~3 ms of sim time and the loop
// body is a handful of AXI reads, so this is deliberately generous.
#define USB_POLL_TIMEOUT              2000000u

// Bound on the EPSKIP self-clear poll. The DMA scan visits all 16 skip bits
// in at most a few dozen AHB clocks, so any value above a few hundred reads
// only ever trips on a real failure.
#define USB_SKIP_POLL_TIMEOUT         20000u

// Bound on the wait for the phase B partial transfer to land. The UVM
// sequence delivers it ~200 us after the endpoint is armed; this budget is
// several milliseconds of simulated time.
#define USB_PARTIAL_POLL_TIMEOUT      50000u

// Number of SETUP packets the UVM sequence issues during enumeration.
// Skip phases start once they have all been answered.
#define USB_ENUM_CTRL_XFERS           7u

// EP command/status list byte offsets (phys_ep * 8, buffer 0).
#define USB_EP_LIST_EP1_OUT_OFFSET    0x010u
#define USB_EP_LIST_EP1_IN_OFFSET     0x018u

// EPSKIP / EPINUSE / INTSTAT bit positions for the endpoints under test.
#define USB_SKIP_BIT_EP1_OUT          (1u << 2)
#define USB_SKIP_BIT_EP1_IN           (1u << 3)
#define USB_EPINUSE_BIT_EP1_OUT       (1u << 2)

// SRAM buffers.
#define USB_SRAM_EP1_OUT_B_BUF        0x200u
#define USB_SRAM_EP1_OUT_C_BUF        0x400u
#define USB_SRAM_EP1_IN_BUF           0x600u

// Transfer sizes.
#define USB_PHASE_A_NBYTES            2048u
#define USB_PHASE_B_NBYTES            2048u
#define USB_PHASE_B_RECEIVED          512u
#define USB_PHASE_C_NBYTES            512u
#define USB_PHASE_D_NBYTES            64u

// EP entry field extraction (see usb.h for the packing macros).
#define USB_EP_ENTRY_GET_NBYTES(e)    (((e) >> 11) & 0x7FFFu)
#define USB_EP_ENTRY_GET_ADDR(e)      ((e) & 0x7FFu)

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static uint32_t usb_skip_errors = 0;

static void check(bool cond, const char *what) {
    if (cond) {
        VPRINTF(LOW, "MCU: PASS - %s\n", what);
    } else {
        usb_skip_errors++;
        VPRINTF(LOW, "MCU: FAIL - %s\n", what);
    }
}

static void usb_ep_entry_write(uint32_t list_offset, uint32_t entry) {
    lsu_write_32(USB_DMA_BASE_ADDR + list_offset, entry);
    // Read back so the SRAM write has retired before the EPSKIP register
    // write is issued on the other AXI port.
    (void)lsu_read_32(USB_DMA_BASE_ADDR + list_offset);
}

static uint32_t usb_ep_entry_read(uint32_t list_offset) {
    return lsu_read_32(USB_DMA_BASE_ADDR + list_offset);
}

// Write one EPSKIP bit and wait for hardware to self-clear it.
// Returns true when hardware cleared the bit within the poll budget.
static bool usb_ep_skip(uint32_t skip_bit, const char *label) {
    uint32_t i;

    lsu_write_32(SOC_USBHSD_EPSKIP, skip_bit);
    VPRINTF(LOW, "MCU: EPSKIP <= 0x%x (%s)\n", skip_bit, label);

    for (i = 0; i < USB_SKIP_POLL_TIMEOUT; i++) {
        if ((lsu_read_32(SOC_USBHSD_EPSKIP) & skip_bit) == 0) {
            VPRINTF(LOW, "MCU: EPSKIP bit 0x%x self-cleared after %d polls\n",
                    skip_bit, i);
            return true;
        }
    }
    VPRINTF(LOW, "MCU: EPSKIP bit 0x%x NEVER self-cleared (EPSKIP=0x%x)\n",
            skip_bit, lsu_read_32(SOC_USBHSD_EPSKIP));
    return false;
}

static void usb_fill_sram(uint32_t offset, uint32_t nbytes, uint32_t pattern) {
    for (uint32_t i = 0; i < nbytes; i += 4)
        lsu_write_32(USB_DMA_BASE_ADDR + offset + i, pattern);
}

// Verify nbytes of SRAM against word[i] == base + i.
static uint32_t usb_check_pattern(uint32_t offset, uint32_t nbytes, uint32_t base) {
    uint32_t errors = 0;
    for (uint32_t i = 0; i < nbytes; i += 4) {
        uint32_t actual   = lsu_read_32(USB_DMA_BASE_ADDR + offset + i);
        uint32_t expected = base + (i / 4u);
        if (actual != expected) {
            if (errors < 8)
                VPRINTF(LOW, "MCU: data mismatch at 0x%x: got 0x%x exp 0x%x\n",
                        offset + i, actual, expected);
            errors++;
        }
    }
    return errors;
}

// -------------------------------------------------------------------------
// Phase E : skip a physical endpoint whose Active bit is already zero.
// Hardware must still self-clear the skip bit, but must NOT raise the
// endpoint interrupt (dma_set_int follows the fetched Active bit).
// -------------------------------------------------------------------------
static void usb_phase_e(void) {
    VPRINTF(LOW, "\nMCU: ===== Phase E: skip inactive EP1 IN =====\n");

    usb_ep_entry_write(USB_EP_LIST_EP1_IN_OFFSET,
                       USB_EP_ENTRY_ADDR(USB_SRAM_EP1_IN_BUF));
    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1IN_MASK);

    check(usb_ep_skip(USB_SKIP_BIT_EP1_IN, "phase E EP1 IN"),
          "E: EPSKIP[3] self-cleared on an inactive endpoint");

    check((lsu_read_32(SOC_USBHSD_INTSTAT) & USBHSD_INTSTAT_EP1IN_MASK) == 0,
          "E: no EP1 IN interrupt raised (Active was already 0)");
}

// -------------------------------------------------------------------------
// Phase A : skip an idle armed EP1 OUT with no bus traffic at all.
// -------------------------------------------------------------------------
static void usb_phase_a(void) {
    uint32_t entry;

    VPRINTF(LOW, "\nMCU: ===== Phase A: skip idle armed EP1 OUT =====\n");

    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);
    lsu_write_32(SOC_USBHSD_EPINUSE, 0);

    entry = USB_EP_ENTRY_ACTIVE
          | USB_EP_ENTRY_NBYTES(USB_PHASE_A_NBYTES)
          | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_B_BUF);
    usb_ep_entry_write(USB_EP_LIST_EP1_OUT_OFFSET, entry);
    VPRINTF(LOW, "MCU: EP1 OUT armed idle (entry=0x%x)\n", entry);

    check(usb_ep_skip(USB_SKIP_BIT_EP1_OUT, "phase A EP1 OUT"),
          "A: EPSKIP[2] self-cleared");

    entry = usb_ep_entry_read(USB_EP_LIST_EP1_OUT_OFFSET);
    VPRINTF(LOW, "MCU: EP1 OUT entry after skip = 0x%x (NBytes=%d addr=0x%x)\n",
            entry, USB_EP_ENTRY_GET_NBYTES(entry), USB_EP_ENTRY_GET_ADDR(entry));

    check((entry & USB_EP_ENTRY_ACTIVE) == 0,
          "A: hardware cleared the Active bit");
    check(USB_EP_ENTRY_GET_NBYTES(entry) == USB_PHASE_A_NBYTES,
          "A: NBytes residual untouched (no data was transferred)");
    check(USB_EP_ENTRY_GET_ADDR(entry) == USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_B_BUF),
          "A: buffer address offset untouched");
    check((lsu_read_32(SOC_USBHSD_INTSTAT) & USBHSD_INTSTAT_EP1OUT_MASK) != 0,
          "A: EP1 OUT interrupt raised by the Active 1->0 transition");
    check((lsu_read_32(SOC_USBHSD_EPINUSE) & USB_EPINUSE_BIT_EP1_OUT) == 0,
          "A: EPINUSE not modified by the skip");

    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);
}

// -------------------------------------------------------------------------
// Phase D : skip an armed IN endpoint that the host never polls.
// -------------------------------------------------------------------------
static void usb_phase_d(void) {
    uint32_t entry;

    VPRINTF(LOW, "\nMCU: ===== Phase D: skip armed EP1 IN =====\n");

    usb_fill_sram(USB_SRAM_EP1_IN_BUF, USB_PHASE_D_NBYTES, 0xD1D1D1D1u);
    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1IN_MASK);

    entry = USB_EP_ENTRY_ACTIVE
          | USB_EP_ENTRY_NBYTES(USB_PHASE_D_NBYTES)
          | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_IN_BUF);
    usb_ep_entry_write(USB_EP_LIST_EP1_IN_OFFSET, entry);
    VPRINTF(LOW, "MCU: EP1 IN armed (entry=0x%x)\n", entry);

    check(usb_ep_skip(USB_SKIP_BIT_EP1_IN, "phase D EP1 IN"),
          "D: EPSKIP[3] self-cleared on an armed IN endpoint");

    entry = usb_ep_entry_read(USB_EP_LIST_EP1_IN_OFFSET);
    VPRINTF(LOW, "MCU: EP1 IN entry after skip = 0x%x (NBytes=%d)\n",
            entry, USB_EP_ENTRY_GET_NBYTES(entry));

    check((entry & USB_EP_ENTRY_ACTIVE) == 0,
          "D: hardware cleared the EP1 IN Active bit");
    check(USB_EP_ENTRY_GET_NBYTES(entry) == USB_PHASE_D_NBYTES,
          "D: EP1 IN NBytes residual untouched (nothing was transmitted)");
    check((lsu_read_32(SOC_USBHSD_INTSTAT) & USBHSD_INTSTAT_EP1IN_MASK) != 0,
          "D: EP1 IN interrupt raised by the Active 1->0 transition");

    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1IN_MASK);
}

// -------------------------------------------------------------------------
// Phase B : arm EP1 OUT for 2048 bytes, let the host deliver a single
// 512 byte packet, then abort the rest of the buffer with a skip.
// -------------------------------------------------------------------------
static void usb_phase_b_arm(void) {
    uint32_t entry;

    VPRINTF(LOW, "\nMCU: ===== Phase B: skip EP1 OUT mid transfer =====\n");

    usb_fill_sram(USB_SRAM_EP1_OUT_B_BUF, USB_PHASE_B_NBYTES, 0xDEDEDEDEu);
    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);

    entry = USB_EP_ENTRY_ACTIVE
          | USB_EP_ENTRY_NBYTES(USB_PHASE_B_NBYTES)
          | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_B_BUF);
    usb_ep_entry_write(USB_EP_LIST_EP1_OUT_OFFSET, entry);
    VPRINTF(LOW, "MCU: EP1 OUT armed for %d bytes (entry=0x%x), waiting for the "
                 "host to deliver %d bytes\n",
            USB_PHASE_B_NBYTES, entry, USB_PHASE_B_RECEIVED);
}

static void usb_phase_b_skip(bool partial_seen, uint32_t entry_before) {
    uint32_t entry;
    uint32_t residual;
    uint32_t errors;

    VPRINTF(LOW, "MCU: entry before skip = 0x%x (NBytes=%d) partial_seen=%d\n",
            entry_before, USB_EP_ENTRY_GET_NBYTES(entry_before),
            (int)partial_seen);

    check(partial_seen,
          "B: hardware updated the EP1 OUT entry after the partial transfer");

    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);

    check(usb_ep_skip(USB_SKIP_BIT_EP1_OUT, "phase B EP1 OUT"),
          "B: EPSKIP[2] self-cleared mid transfer");

    entry    = usb_ep_entry_read(USB_EP_LIST_EP1_OUT_OFFSET);
    residual = USB_EP_ENTRY_GET_NBYTES(entry);
    VPRINTF(LOW, "MCU: EP1 OUT entry after skip = 0x%x (NBytes=%d addr=0x%x)\n",
            entry, residual, USB_EP_ENTRY_GET_ADDR(entry));

    check((entry & USB_EP_ENTRY_ACTIVE) == 0,
          "B: hardware cleared the Active bit mid transfer");
    check(residual == (USB_PHASE_B_NBYTES - USB_PHASE_B_RECEIVED),
          "B: NBytes residual equals armed minus received (1536)");
    check((lsu_read_32(SOC_USBHSD_INTSTAT) & USBHSD_INTSTAT_EP1OUT_MASK) != 0,
          "B: EP1 OUT interrupt raised by the skip");

    errors = usb_check_pattern(USB_SRAM_EP1_OUT_B_BUF, USB_PHASE_B_RECEIVED,
                               0xB0000000u);
    check(errors == 0, "B: the 512 bytes received before the skip are intact");

    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);
}

// -------------------------------------------------------------------------
// Phase C : re-arm the skipped endpoint and run a normal transfer to prove
// the endpoint is fully usable again.
// -------------------------------------------------------------------------
static void usb_phase_c_arm(void) {
    uint32_t entry;

    VPRINTF(LOW, "\nMCU: ===== Phase C: EP1 OUT recovery after skip =====\n");

    usb_fill_sram(USB_SRAM_EP1_OUT_C_BUF, USB_PHASE_C_NBYTES, 0xCECECECEu);
    lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);

    entry = USB_EP_ENTRY_ACTIVE
          | USB_EP_ENTRY_NBYTES(USB_PHASE_C_NBYTES)
          | USB_EP_ENTRY_ADDR(USB_SRAM_EP1_OUT_C_BUF);
    usb_ep_entry_write(USB_EP_LIST_EP1_OUT_OFFSET, entry);
    VPRINTF(LOW, "MCU: EP1 OUT re-armed after skip (entry=0x%x)\n", entry);
}

static void usb_phase_c_check(void) {
    uint32_t entry  = usb_ep_entry_read(USB_EP_LIST_EP1_OUT_OFFSET);
    uint32_t errors;

    VPRINTF(LOW, "MCU: EP1 OUT entry after recovery transfer = 0x%x (NBytes=%d)\n",
            entry, USB_EP_ENTRY_GET_NBYTES(entry));

    check((entry & USB_EP_ENTRY_ACTIVE) == 0,
          "C: Active cleared by normal completion after the skip");
    check(USB_EP_ENTRY_GET_NBYTES(entry) == 0,
          "C: NBytes residual is zero (full 512 bytes received)");

    errors = usb_check_pattern(USB_SRAM_EP1_OUT_C_BUF, USB_PHASE_C_NBYTES,
                               0xC0000000u);
    check(errors == 0, "C: recovered endpoint received the full data pattern");
}

// -------------------------------------------------------------------------

enum usb_skip_phase {
    PH_ENUM = 0,
    PH_B_WAIT,
    PH_C_WAIT,
    PH_DONE
};

void main(void) {
    uint32_t reg_data;
    uint32_t intstat;
    uint32_t poll_count;
    uint32_t ctrl_xfers  = 0;
    uint32_t partial_polls = 0;
    uint32_t entry_before  = 0;
    bool     partial_seen  = false;
    enum usb_skip_phase phase = PH_ENUM;

    VPRINTF(LOW, "=================\nMCU: USB HS device EPSKIP test\n=================\n\n");

    boot_mcu();
    boot_usb_core();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT && phase != PH_DONE;
         poll_count++) {

        usb_handle_bus_reset();

        reg_data = lsu_read_32(SOC_USBHSD_DEVCMDSTAT);
        intstat  = lsu_read_32(SOC_USBHSD_INTSTAT);

        if (intstat & USBHSD_INTSTAT_DEV_INT_MASK) {
            if (reg_data & USBHSD_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (phase != PH_ENUM) {
                    VPRINTF(LOW, "MCU: unexpected bus reset in phase %d\n",
                            (int)phase);
                }
            }
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_DEV_INT_MASK);
        }

        // EP0 OUT: SETUP packets drive enumeration.
        if (intstat & USBHSD_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0OUT_MASK);
            if (reg_data & USBHSD_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
                ctrl_xfers++;
                VPRINTF(LOW, "MCU: control transfer %d handled\n", ctrl_xfers);

                if (phase == PH_ENUM && ctrl_xfers >= USB_ENUM_CTRL_XFERS) {
                    VPRINTF(LOW, "MCU: enumeration complete, starting SKIP phases\n");
                    // Register only phases: no bus traffic is required, the
                    // DMA skip scan runs continuously.
                    usb_phase_e();
                    usb_phase_a();
                    usb_phase_d();
                    usb_phase_b_arm();
                    partial_polls = 0;
                    phase = PH_B_WAIT;
                }
            }
        }

        if (intstat & USBHSD_INTSTAT_EP0IN_MASK)
            lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP0IN_MASK);

        // Phase B: wait for the host packet to be written back into the EP
        // entry (NBytes decremented) and then abort the remainder.
        if (phase == PH_B_WAIT) {
            entry_before = usb_ep_entry_read(USB_EP_LIST_EP1_OUT_OFFSET);
            if (USB_EP_ENTRY_GET_NBYTES(entry_before) != USB_PHASE_B_NBYTES ||
                (entry_before & USB_EP_ENTRY_ACTIVE) == 0) {
                partial_seen = true;
            }
            partial_polls++;

            if (partial_seen || partial_polls >= USB_PARTIAL_POLL_TIMEOUT) {
                usb_phase_b_skip(partial_seen, entry_before);
                usb_phase_c_arm();
                phase = PH_C_WAIT;
            }
        } else if (phase == PH_C_WAIT) {
            if (intstat & USBHSD_INTSTAT_EP1OUT_MASK) {
                lsu_write_32(SOC_USBHSD_INTSTAT, USBHSD_INTSTAT_EP1OUT_MASK);
                usb_phase_c_check();
                phase = PH_DONE;
            }
        }

        if (poll_count % 200000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] phase=%d DEVCMDSTAT=0x%x INTSTAT=0x%x "
                         "EPSKIP=0x%x\n",
                    poll_count, (int)phase, reg_data, intstat,
                    lsu_read_32(SOC_USBHSD_EPSKIP));
        }
    }

    if (phase != PH_DONE) {
        usb_skip_errors++;
        VPRINTF(LOW, "MCU: FAIL - TIMEOUT in phase %d (ctrl_xfers=%d)\n",
                (int)phase, ctrl_xfers);
    }

    if (usb_skip_errors == 0)
        VPRINTF(LOW, "\nMCU: USB HS dev SKIP test - PASSED\n");
    else
        VPRINTF(LOW, "\nMCU: USB HS dev SKIP test - FAILED (%d errors)\n",
                usb_skip_errors);

    VPRINTF(LOW, "MCU: USB HS device EPSKIP test - halting\n");
    csr_write_mpmc_halt();
}
