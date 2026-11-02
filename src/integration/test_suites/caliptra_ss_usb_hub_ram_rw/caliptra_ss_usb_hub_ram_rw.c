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
// Description: USB HUB descriptor-array (ep0_mem) read/write and write-lock
//  test for the Caliptra Subsystem.
//
//  The embedded USB hub keeps its descriptors (device, configuration, hub
//  class, qualifier, other-speed config, BOS) and its SETUP-match table in an
//  internal 196-word (C_NWORDS) 32-bit flip-flop array named ep0_mem inside
//  the compound IP (usb_ep0_hub_descr.m.vhdl). The whole array is reachable
//  from the MCU LSU AXI master over the hub_axi aperture at
//  USB_HUB_DESC_DEVICE_BASE (SOC_USB_COMBO_HUB_DESCRIPTOR_LOW_BASE_ADDR =
//  0x2000_1000); word i lives at base + i*4. The aperture spans
//  0x2000_1000 .. 0x2000_130F, which is exactly 196 words, and word 12 is
//  SOC_USB_COMBO_HUB_CONTROL (0x2000_1030) = C_HUB_CS, which confirms the base.
//  No USB link bring-up and no USB traffic are required to access it - this is
//  a standalone memory test.
//
//  Write-lock rule (from the RTL):
//    hub_write_lock <= ep0_mem(C_HUB_CS)(0) and ep0_mem(C_HUB_CS)(16)
//    write allowed only if (hub_write_lock='0' OR waddr=C_HUB_CS) and waddr<196
//  C_HUB_CS is word 12 (byte offset 0x30), the Hub Control/Status register:
//    bit 0  = HUB_EN, bit 16 = HUB_CONNECT (DCON).
//  So the array is writable while at most one of HUB_EN / HUB_CONNECT is set,
//  and freezes (all words except the control word) once BOTH are set. The
//  control word is ALWAYS writable (explicitly exempted from the lock), so
//  firmware can clear HUB_CONNECT afterwards to release the lock again.
//
//  Methodology (Option B, three iterations):
//    For each of USB_HUB_RAM_LOOPS loops:
//      Phase A - UNLOCKED (HUB_EN=1, HUB_CONNECT=0): the lock is deasserted.
//        For every sweepable word, read the current value, write a random
//        value forced to differ from it, read back, and require the readback to
//        equal the written value. This proves each word is writable when
//        unlocked and that neighboring words decode independently.
//      Phase B - LOCKED (HUB_EN=1, HUB_CONNECT=1): the lock is asserted.
//        First capture the current value of every sweepable word into a
//        shadow array (this is the post-lock baseline). Then, for every
//        sweepable word, attempt a random write and read back, requiring the
//        readback to still equal the captured baseline. This proves the lock
//        rejects writes to the descriptor array. Writing all attempts and
//        comparing against the captured baseline proves the array is frozen.
//      Between loops the control word is cleared (HUB_EN=0, HUB_CONNECT=0) so
//        the next loop starts from a clean, unlocked state.
//
//  Two words are excluded from the random sweep:
//    - word 12 (C_HUB_CS, the Hub Control/Status register): it is always
//      writable even under the lock and it holds the enable/connect controls,
//      so a random write there would change the lock state or disconnect the
//      hub mid-test. It is driven only by the explicit phase-control writes
//      below.
//    - word 15 (C_HUB_PHY, the ULPI PHY access register): hardware writes into
//      this word on its own (the PHY read data is captured into bits [23:16]
//      and PHY_START bit 25 is self-clearing), so a random value written there
//      does not read back unchanged and the unlocked write check would report a
//      false failure.
//  Both constants come from usb_ep0_hub_descr.m.vhdl.

//
//  This test drives no USB traffic, so the descriptor array is free to be
//  perturbed. The companion UVM sequence (caliptra_ss_usb_mem_rw_sequence)
//  simply holds the run phase open long enough for this firmware to finish and
//  report its verdict via the DEBUG_OUT control byte.

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
// Hub descriptor-array geometry.
//
// C_NWORDS = 196 32-bit words (usb_ep0_hub_descr.m.vhdl). Three words are
// excluded from the random sweep:
//   C_HUB_CS  = word 12: Hub Control/Status register, always writable even
//               under the lock, so it is driven only by the explicit
//               phase-control writes and never randomized.
//   C_HUB_LPM = word 13: Hub LPM L1 register. PROC_REG_WRITE assigns
//               ep0_mem(C_HUB_LPM)(3 downto 0) <= hub_lpm_hird_hw on every
//               clock, unconditionally, so bits [3:0] always read back as the
//               hardware HIRD value (0 when no LPM transaction is in flight)
//               regardless of what was written.
//   C_HUB_PHY = word 15: ULPI PHY access register, partly hardware-written
//               (PHY read data lands in bits [23:16] and PHY_START bit 25
//               self-clears), so it does not read back what was written.
// ---------------------------------------------------------------------------
#define USB_HUB_RAM_WORDS 196u   // C_NWORDS: total words in the ep0_mem array
#define USB_HUB_CS_WORD   12u    // C_HUB_CS:  Hub Control/Status register word
#define USB_HUB_LPM_WORD  13u    // C_HUB_LPM: Hub LPM L1 register word
#define USB_HUB_PHY_WORD  15u    // C_HUB_PHY: ULPI PHY access register word
#define USB_HUB_RAM_LOOPS 3u     // number of unlocked/locked iterations

// Number of words actually swept (total minus the three excluded above).
#define USB_HUB_RAM_SWEPT_WORDS (USB_HUB_RAM_WORDS - 3u)

// True for the words excluded from the random sweep.
static inline int hub_word_skipped(uint32_t i) {
    return (i == USB_HUB_CS_WORD) ||
           (i == USB_HUB_LPM_WORD) ||
           (i == USB_HUB_PHY_WORD);
}

// Per-word byte address of hub word index i.
static inline uint32_t hub_word_addr(uint32_t i) {
    return USB_HUB_DESC_DEVICE_BASE + (i * 4u);
}

// Post-lock baseline of every word (the skipped slots are present but unused).
static uint32_t shadow_val[USB_HUB_RAM_WORDS];

// Phase A: with the array UNLOCKED (HUB_EN=1, HUB_CONNECT=0), write a random
// value (forced to differ from the current contents) to every sweepable word
// and require the write to take effect. Returns the number of mismatches.
static int hub_unlocked_check(uint32_t loop) {
    int errors = 0;
    VPRINTF(LOW, "\n--- USB HUB ep0_mem UNLOCKED write loop %d/%d: %d words ---\n",
            loop + 1u, USB_HUB_RAM_LOOPS, USB_HUB_RAM_WORDS);

    // Ensure the array is unlocked with a clean edge, then set HUB_EN only.
    // HUB_CONNECT stays 0, so hub_write_lock = HUB_EN and HUB_CONNECT = 0.
    lsu_write_32(USB_HUB_CTRL, 0u);
    lsu_write_32(USB_HUB_CTRL, USBHUB_CTRL_HUB_EN_MASK);

    for (uint32_t i = 0; i < USB_HUB_RAM_WORDS; i++) {
        if (hub_word_skipped(i)) {
            continue;
        }
        uint32_t addr = hub_word_addr(i);
        uint32_t orig = lsu_read_32(addr);
        uint32_t val  = xorshift32();
        if (val == orig) {
            val = ~orig;  // force a real change so the write is observable
        }
        lsu_write_32(addr, val);
        uint32_t rd = lsu_read_32(addr);
        if (rd != val) {
            VPRINTF(LOW, "ERROR: HUB ep0_mem UNLOCKED @0x%x write dropped: "
                    "wrote 0x%x got 0x%x\n", addr, val, rd);
            errors++;
        }
    }
    if (errors == 0) {
        VPRINTF(LOW, "HUB ep0_mem unlocked write ok (%d words)\n",
                USB_HUB_RAM_SWEPT_WORDS);
    }
    return errors;
}

// Phase B: with the array LOCKED (HUB_EN=1, HUB_CONNECT=1), capture the
// post-lock baseline of every sweepable word, then attempt a random write to
// each and require the contents to be preserved. Returns the number of words
// the lock failed to protect.
static int hub_locked_check(uint32_t loop) {
    int errors = 0;
    VPRINTF(LOW, "\n--- USB HUB ep0_mem LOCKED preserve loop %d/%d: %d words ---\n",
            loop + 1u, USB_HUB_RAM_LOOPS, USB_HUB_RAM_WORDS);

    // Assert both HUB_EN and HUB_CONNECT: hub_write_lock now = 1, freezing every
    // word except the always-writable control word.
    lsu_write_32(USB_HUB_CTRL,
                 USBHUB_CTRL_HUB_EN_MASK | USBHUB_CTRL_HUB_CONNECT_MASK);

    // Capture the post-lock baseline in one pass so the compare is a deferred
    // read-back after all write attempts (proves the whole array is frozen).
    for (uint32_t i = 0; i < USB_HUB_RAM_WORDS; i++) {
        if (hub_word_skipped(i)) {
            continue;
        }
        shadow_val[i] = lsu_read_32(hub_word_addr(i));
    }

    // Attempt to corrupt every word with a random value; the lock must drop it.
    for (uint32_t i = 0; i < USB_HUB_RAM_WORDS; i++) {
        if (hub_word_skipped(i)) {
            continue;
        }
        lsu_write_32(hub_word_addr(i), xorshift32());
    }

    // Deferred read-back: every word must still hold its captured baseline.
    for (uint32_t i = 0; i < USB_HUB_RAM_WORDS; i++) {
        if (hub_word_skipped(i)) {
            continue;
        }
        uint32_t addr = hub_word_addr(i);
        uint32_t rd   = lsu_read_32(addr);
        if (rd != shadow_val[i]) {
            VPRINTF(LOW, "ERROR: HUB ep0_mem LOCKED @0x%x not preserved: "
                    "baseline 0x%x got 0x%x  <-- write-lock leak\n",
                    addr, shadow_val[i], rd);
            errors++;
        }
    }
    if (errors == 0) {
        VPRINTF(LOW, "HUB ep0_mem locked preserve ok (%d words)\n",
                USB_HUB_RAM_SWEPT_WORDS);
    }

    // Release the lock for the next loop: clearing the control word is always
    // allowed.
    lsu_write_32(USB_HUB_CTRL, 0u);
    return errors;
}

void main(void) {

    int error_count = 0;

    VPRINTF(LOW, "=================\nMCU: USB HUB ep0_mem RW / write-lock test\n=================\n\n");

    // Standard MCU boot sequence. This is a standalone memory-access test: no
    // USB core bring-up and no USB traffic is generated, so the hub descriptor
    // array is free scratch space that can be perturbed safely.
    boot_mcu();

    // Three iterations of the unlocked-then-locked loop.
    for (uint32_t loop = 0; loop < USB_HUB_RAM_LOOPS; loop++) {
        error_count += hub_unlocked_check(loop);
        error_count += hub_locked_check(loop);
    }

    VPRINTF(LOW, "\nMCU: USB HUB ep0_mem RW test complete, error_count = %d\n",
            error_count);

    if (error_count == 0) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }

    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
