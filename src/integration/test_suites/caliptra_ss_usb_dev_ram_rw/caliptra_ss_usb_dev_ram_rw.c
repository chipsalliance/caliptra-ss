//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
//
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
// Description: USB device-controller RAM (SRAM/DMA region) random read/write
//  test for the Caliptra Subsystem, exercising the DMA/SRAM window of the
//  compile-time-selected embedded device controller (USBDC0 by default,
//  USBDC1 when built with -DUSB_DEV_SEL=1).
//
//  The DMA/SRAM region is directly reachable from the MCU LSU AXI master with
//  no RTL change and no USB core bring-up: the compound wrapper splits each
//  device aperture into a register region (offset < DEV_REG_ADDR_TOP = 0x100)
//  and a DMA/SRAM region (offset >= 0x100). USB_DEV_DMA_BASE_ADDR is therefore
//  the base of the RAM window (0x2000_1100 for DEV0, 0x2001_0100 for DEV1).
//
//  RAM geometry (see claude_md/12_usb_memory_interface.md): each entity RAM is
//  512 x 64-bit = 4 KB. The TB behavioral model (caliptra_ss_top_tb.sv) indexes
//  usb_dev0_sram/usb_dev1_sram by the AXI address, and the MCU accesses it as
//  32-bit words via lsu_write_32 / lsu_read_32. The RAM window addressable from
//  the MCU therefore spans the DMA base up to the end of the 4 KB s5 NIC window
//  (0x2000_1FFF), i.e. USB_DEV_RAM_WORDS 32-bit words at a 4-byte stride.
//
//  Methodology:
//    Phase 1 - deterministic sweep: write a known per-address pattern
//              (addr XOR seed) to every word in the window, then read every
//              word back and compare. This catches gross addressing / aliasing
//              faults cleanly before the random phase runs.
//    Phase 2 - random walk: for USB_DEV_RAM_ITERS iterations pick a random word
//              in the window and a random 32-bit value (both from xorshift32),
//              write it, and record the last value written to each touched word
//              in a shadow array. After all writes, read every touched word
//              back and compare against the shadow. Writing all values first
//              and comparing afterward proves the words are independent storage
//              (a later write to word A must not disturb word B). This random
//              walk is repeated USB_DEV_RAM_LOOPS times; each loop clears the
//              shadow and draws fresh random word/value pairs, so successive
//              loops cover different addresses and re-verify independent storage.
//
//  This is a standalone RAM-access test: it drives no USB traffic, brings up no
//  hub and no USB core, and runs no DMA, so the whole RAM window is free scratch
//  space and can be randomized without disturbing any live endpoint. The
//  companion UVM sequence (caliptra_ss_usb_dev_ram_rw_sequence) simply holds the
//  run phase open long enough for this firmware to finish and report its
//  verdict via the DEBUG_OUT control byte.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// ---------------------------------------------------------------------------
// RAM window geometry.
//
// The DMA/SRAM region starts at USB_DEV_DMA_BASE_ADDR and runs to the end of
// the 4 KB s5 NIC window (last word at base_of_aperture + 0xFFC). With the DMA
// base at offset 0x100 from the aperture base, the number of 32-bit words from
// the DMA base to the end of the aperture is (0x1000 - 0x100) / 4 = 0x3C0 = 960.
// Bound the sweep/shadow to a fixed, comfortably-sized count so the shadow array
// fits easily in MCU data memory.
// ---------------------------------------------------------------------------
#define USB_DEV_RAM_WORDS 960u   // 32-bit words from USB_DEV_DMA_BASE_ADDR to aperture end
#define USB_DEV_RAM_ITERS 256u   // number of random word accesses per phase-2 loop
#define USB_DEV_RAM_LOOPS 5u     // number of random-walk loops in phase 2


// Per-word byte address of RAM word index i.
static inline uint32_t ram_word_addr(uint32_t i) {
    return USB_DEV_DMA_BASE_ADDR + (i * 4u);
}

// Deterministic pattern for a given word index. Mixing the index with a fixed
// salt makes neighboring words hold distinct values, so an address decode that
// returns the wrong word is caught by the compare.
static inline uint32_t sweep_pattern(uint32_t i) {
    return (i * 0x9E3779B1u) ^ 0xA5A5A5A5u;
}

// Phase 1: write a known pattern to every word, then read every word back and
// compare. Returns the number of mismatches.
static int ram_sweep_check(void) {
    int errors = 0;
    VPRINTF(LOW, "\n--- USB DEV RAM deterministic sweep: base 0x%x, %d words ---\n",
            (uint32_t)USB_DEV_DMA_BASE_ADDR, USB_DEV_RAM_WORDS);

    for (uint32_t i = 0; i < USB_DEV_RAM_WORDS; i++) {
        lsu_write_32(ram_word_addr(i), sweep_pattern(i));
    }
    for (uint32_t i = 0; i < USB_DEV_RAM_WORDS; i++) {
        uint32_t exp = sweep_pattern(i);
        uint32_t rd  = lsu_read_32(ram_word_addr(i));
        if (rd != exp) {
            VPRINTF(LOW, "ERROR: DEV RAM sweep @0x%x mismatch: wrote 0x%x got 0x%x\n",
                    ram_word_addr(i), exp, rd);
            errors++;
        }
    }
    if (errors == 0) {
        VPRINTF(LOW, "DEV RAM deterministic sweep ok (%d words)\n", USB_DEV_RAM_WORDS);
    }
    return errors;
}

// Phase 2: random write walk with deferred read-back compare. The shadow holds
// the last value written to each word so that words never touched keep their
// swept value (which we do NOT re-check here - only touched words are compared).
// A companion "touched" flag marks which words were written in this phase.
static uint32_t shadow_val[USB_DEV_RAM_WORDS];
static uint8_t  shadow_touched[USB_DEV_RAM_WORDS];

static int ram_random_check(uint32_t loop) {
    int errors = 0;
    VPRINTF(LOW, "\n--- USB DEV RAM random walk loop %d/%d: %d iterations over %d words ---\n",
            loop + 1u, USB_DEV_RAM_LOOPS, USB_DEV_RAM_ITERS, USB_DEV_RAM_WORDS);

    for (uint32_t i = 0; i < USB_DEV_RAM_WORDS; i++) {
        shadow_touched[i] = 0u;
    }

    // Write phase: pick random word + random value, write, and record.

    for (uint32_t n = 0; n < USB_DEV_RAM_ITERS; n++) {
        uint32_t idx = xorshift32() % USB_DEV_RAM_WORDS;
        uint32_t val = xorshift32();
        lsu_write_32(ram_word_addr(idx), val);
        shadow_val[idx]     = val;
        shadow_touched[idx] = 1u;
    }

    // Read-back phase: verify every touched word still holds its last value.
    for (uint32_t i = 0; i < USB_DEV_RAM_WORDS; i++) {
        if (!shadow_touched[i]) {
            continue;
        }
        uint32_t rd = lsu_read_32(ram_word_addr(i));
        if (rd != shadow_val[i]) {
            VPRINTF(LOW, "ERROR: DEV RAM random @0x%x mismatch: wrote 0x%x got 0x%x\n",
                    ram_word_addr(i), shadow_val[i], rd);
            errors++;
        }
    }
    if (errors == 0) {
        VPRINTF(LOW, "DEV RAM random walk ok\n");
    }
    return errors;
}

void main(void) {

    int error_count = 0;

    VPRINTF(LOW, "=================\nMCU: USB dev RAM RW test\n=================\n\n");

    // Standard MCU boot sequence. This is a standalone RAM-access test, so no
    // USB core bring-up and no USB traffic is generated; the RAM window is free
    // scratch space and can be randomized safely.
    boot_mcu();

    // Phase 1: deterministic full-window sweep.
    error_count += ram_sweep_check();

    // Phase 2: random write / deferred read-back compare, repeated over
    // USB_DEV_RAM_LOOPS independent loops of fresh random word/value pairs.
    for (uint32_t loop = 0; loop < USB_DEV_RAM_LOOPS; loop++) {
        error_count += ram_random_check(loop);
    }


    VPRINTF(LOW, "\nMCU: USB dev RAM RW test complete, error_count = %d\n",
            error_count);

    if (error_count == 0) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
