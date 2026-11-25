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
// Description: USB HS EP-info rate-feedback / descriptor toggle test firmware
//              for the Caliptra SS (suffix USB_DMA_EPINFO_RATE_FEEDBACK).
//
// PURPOSE. Code coverage of the READ_EPINFO decode in
// third_party/usb2/src/usb_hub_composite_device/RTL/RTL/usb_dma.m.vhdl. This
// integration builds usb_dma with RAM_DATAWIDTH = 64, so each EP-list read
// returns two descriptor words and epinfo_addr(2) selects which one is decoded:
//   lower word, buffer 0 (lines 366-397)  bits 28/27/26 = TR / TV-RF / T
//   upper word, buffer 1 (lines 332-363)  bits 60/59/58 = TR / TV-RF / T
// epinfo_addr(2) is '1' when the endpoint's EPINUSE bit is set
// (usb_dma.m.vhdl:1167-1169), so firmware chooses the decoded word by writing
// EPINUSE before each leg.
//
// TARGET LINES AND THE LEG THAT HITS THEM
//   leg 0  buffer 0, TR=0 T=0 RF=1  rate-feedback mode  -> 386, 387
//   leg 1  buffer 0, TR=1 TV=1      set toggle          -> 376
//   leg 2  buffer 1, TR=0 T=0 RF=1  rate-feedback mode  -> 352, 353
//   leg 3  buffer 1, TR=1 TV=1      set toggle          -> 341, 342, 346
//   leg 4  buffer 1, TR=1 TV=0      clear toggle        -> 341, 344, 346
// Lines 334, 356 and 357 need buffer 1 AND endpoint 0, which cannot happen
// (EP0 only reaches the upper word through a SETUP, which takes the earlier
// branch at line 278, and usb_reg_if.m.vhdl:234 ties the EP0 EPINUSE bits to
// '0'). They are waived, not stimulated - see claude_md note 40.
//
// WHY THIS LEG ORDER. Each leg's descriptor fetch re-establishes the device
// data toggle before the DATA packet is checked (TR loads TV, rate-feedback
// mode clears it, usb_reg_if.m.vhdl:259-262). The host carries a running bulk
// OUT toggle that flips on every ACK, so starting from DATA0 it sends
// DATA0, DATA1, DATA0, DATA1, DATA0 for legs 0..4. The legs are ordered so the
// device toggle set at each fetch equals that PID:
//   leg 0 RF clears -> 0 = DATA0   leg 1 TV=1 -> 1 = DATA1
//   leg 2 RF clears -> 0 = DATA0   leg 3 TV=1 -> 1 = DATA1
//   leg 4 TV=0      -> 0 = DATA0
// so every packet is consumed and every leg completes. That makes the
// received payload the verdict: if a set/clear path did not act, the PID would
// mismatch, the device would ACK and DISCARD the packet (usb_pie.m.vhdl:
// 2746-2760), Active would never clear and the leg would time out here.
//
// ENDPOINT. EP5 OUT: hardware backed (USB_C_DEV0_NBPHYSEP = 28), touched by
// no other test, and zeroed by usb_boot(). Physical endpoint index = 2*5 = 10,
// which is the EPINUSE / EPTOGGLE / INTSTAT bit used below.
//
// EPBUFCFG is deliberately left at single buffering, so the hardware does NOT
// flip EPINUSE on completion (usb_reg_if.m.vhdl:786-792 requires the
// double-buffer bit); EPINUSE is therefore fully firmware controlled.
//
// Verdict: FAIL-only, total_errors never reset, one TB_CMD_TEST_FAIL at the
// end. TB_CMD_TEST_PASS is never sent (it would finish the run before the UVM
// final_phase).

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

#define USB_POLL_TIMEOUT                 60000

// EP5 OUT descriptors: endpoint N OUT buffer 0 is at 0x010 + (N-1)*0x10,
// buffer 1 is the next word.
#define USB_RF_EP                        5u
#define USB_RF_EP_PHYS_BIT               (1u << (2u * USB_RF_EP))
#define USB_EP_LIST_RF_OUT_BUF0_OFFSET   0x050u
#define USB_EP_LIST_RF_OUT_BUF1_OFFSET   0x054u

// 64-byte aligned data buffers, after the EP0 buffers (0x000-0x1FF).
#define USB_SRAM_RF_BUF0_OFFSET          0x200u
#define USB_SRAM_RF_BUF1_OFFSET          0x240u

// One short HS bulk packet per leg. Must match the UVM sequence.
#define USB_RF_LEG_BYTES                 8u
#define USB_RF_NUM_LEGS                  5u

// Bit 27 read as the rate-feedback selector: with TR=0 and T=0 on a non-zero
// endpoint, RF=1 selects rate-feedback mode (usb_dma.m.vhdl:347 / 381). It is
// the same physical bit as USB_EP_ENTRY_TOGGLE_VALUE_DATA1; the separate name
// states which meaning each leg relies on.
#define USB_EP_ENTRY_RATE_FEEDBACK       (1u << 27)

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

static uint32_t total_errors = 0;

typedef struct {
    uint32_t    buf;             // 0 = lower word / buffer 0, 1 = upper word
    uint32_t    mode_bits;       // TR / TV-RF / T bits of the descriptor
    uint32_t    expect_toggle;   // EPTOGGLE bit expected after completion
    const char *name;
} rf_leg_t;

// expect_toggle is reported, not asserted. It follows from usb_dma.m.vhdl:
// the fetch sets/clears the toggle, and on completion it is flipped only when
// (T=0 and RF/TV=0) or (T=1 and RF/TV=1) (lines 573-581 / 650-657), i.e. only
// on leg 4.
static const rf_leg_t rf_legs[USB_RF_NUM_LEGS] = {
    { 0u, USB_EP_ENTRY_RATE_FEEDBACK,                                       0u,
      "buf0 rate-feedback (386-387)" },
    { 0u, USB_EP_ENTRY_TOGGLE_RESET | USB_EP_ENTRY_TOGGLE_VALUE_DATA1,      1u,
      "buf0 TR=1 TV=1 set toggle (376)" },
    { 1u, USB_EP_ENTRY_RATE_FEEDBACK,                                       0u,
      "buf1 rate-feedback (352-353)" },
    { 1u, USB_EP_ENTRY_TOGGLE_RESET | USB_EP_ENTRY_TOGGLE_VALUE_DATA1,      1u,
      "buf1 TR=1 TV=1 set toggle (341-342, 346)" },
    { 1u, USB_EP_ENTRY_TOGGLE_RESET | USB_EP_ENTRY_TOGGLE_VALUE_DATA0,      1u,
      "buf1 TR=1 TV=0 clear toggle (341, 344, 346)" },
};

static uint32_t rf_desc_addr(uint32_t buf) {
    return USB_DMA_BASE_ADDR +
           (buf ? USB_EP_LIST_RF_OUT_BUF1_OFFSET : USB_EP_LIST_RF_OUT_BUF0_OFFSET);
}

static uint32_t rf_buf_offset(uint32_t buf) {
    return buf ? USB_SRAM_RF_BUF1_OFFSET : USB_SRAM_RF_BUF0_OFFSET;
}

// Expected payload word for a leg: byte i = 0x10*(leg+1) + i. Must match the
// UVM sequence's build_leg_payload().
static uint32_t rf_expected_word(uint32_t leg, uint32_t word) {
    uint32_t base = 0x10u * (leg + 1u) + 4u * word;
    return (base) | ((base + 1u) << 8) | ((base + 2u) << 16) | ((base + 3u) << 24);
}

// Arm one leg. Both EP5 OUT words are inactive at this point (never armed, or
// Active cleared by the completion of the previous leg), so rewriting them is
// legal. The unused word is zeroed so a stray fetch of it only NAKs.
static void rf_arm_leg(uint32_t leg) {
    const rf_leg_t *l = &rf_legs[leg];
    uint32_t desc = USB_EP_ENTRY_ACTIVE
                  | l->mode_bits
                  | USB_EP_ENTRY_NBYTES(USB_RF_LEG_BYTES)
                  | USB_EP_ENTRY_ADDR(rf_buf_offset(l->buf));
    uint32_t inuse;

    // Clear the target buffer so stale data from a previous leg cannot pass.
    lsu_write_32(USB_DMA_BASE_ADDR + rf_buf_offset(l->buf),      0u);
    lsu_write_32(USB_DMA_BASE_ADDR + rf_buf_offset(l->buf) + 4u, 0u);

    lsu_write_32(rf_desc_addr(l->buf ? 0u : 1u), 0u);
    lsu_write_32(rf_desc_addr(l->buf), desc);

    inuse = lsu_read_32(USB_DEV_EPINUSE);
    if (l->buf) {
        inuse |= USB_RF_EP_PHYS_BIT;
    } else {
        inuse &= ~USB_RF_EP_PHYS_BIT;
    }
    lsu_write_32(USB_DEV_EPINUSE, inuse);

    VPRINTF(LOW, "MCU: RF leg %d armed - %s desc@0x%x=0x%x EPINUSE=0x%x EPTOGGLE=0x%x\n",
            leg, l->name, rf_desc_addr(l->buf), lsu_read_32(rf_desc_addr(l->buf)),
            lsu_read_32(USB_DEV_EPINUSE), lsu_read_32(USB_DEV_EPTOGGLE));

    if (((lsu_read_32(USB_DEV_EPINUSE) & USB_RF_EP_PHYS_BIT) != 0u) != (l->buf != 0u)) {
        VPRINTF(LOW, "MCU: FAIL - RF leg %d EPINUSE bit 10 did not take (0x%x)\n",
                leg, lsu_read_32(USB_DEV_EPINUSE));
        total_errors++;
    }
}

// Check a completed leg: Active cleared, payload matches, toggle reported.
static void rf_check_leg(uint32_t leg) {
    const rf_leg_t *l = &rf_legs[leg];
    uint32_t desc   = lsu_read_32(rf_desc_addr(l->buf));
    uint32_t w0     = lsu_read_32(USB_DMA_BASE_ADDR + rf_buf_offset(l->buf));
    uint32_t w1     = lsu_read_32(USB_DMA_BASE_ADDR + rf_buf_offset(l->buf) + 4u);
    uint32_t toggle = (lsu_read_32(USB_DEV_EPTOGGLE) & USB_RF_EP_PHYS_BIT) ? 1u : 0u;

    VPRINTF(LOW, "MCU: RF leg %d done - desc=0x%x data=0x%x 0x%x EPTOGGLE[10]=%d (expected %d)\n",
            leg, desc, w0, w1, toggle, l->expect_toggle);

    if (desc & USB_EP_ENTRY_ACTIVE) {
        VPRINTF(LOW, "MCU: FAIL - RF leg %d interrupt seen but Active still set (0x%x)\n",
                leg, desc);
        total_errors++;
    }
    if (w0 != rf_expected_word(leg, 0u) || w1 != rf_expected_word(leg, 1u)) {
        VPRINTF(LOW, "MCU: FAIL - RF leg %d payload 0x%x 0x%x, expected 0x%x 0x%x\n",
                leg, w0, w1, rf_expected_word(leg, 0u), rf_expected_word(leg, 1u));
        total_errors++;
    }
    if (toggle != l->expect_toggle) {
        // Reported only: the expectation is derived from RTL reading and has
        // not been confirmed in simulation yet.
        VPRINTF(LOW, "MCU: NOTE - RF leg %d EPTOGGLE[10]=%d differs from the RTL-derived %d\n",
                leg, toggle, l->expect_toggle);
    }
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t leg       = 0u;
    bool     leg_armed = false;

    VPRINTF(LOW, "=================\nMCU: USB HS EP-info rate-feedback test\n=================\n\n");

    boot_mcu();
    boot_usb_core_hub();
    usb_hub_connect();
    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering USB event loop\n");

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT && leg < USB_RF_NUM_LEGS; poll_count++) {

        usb_handle_bus_reset();
        reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);

        if (reg_data & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
                usb_handle_bus_reset();
                if (leg_armed) {
                    // A bus reset in the middle of the leg sequence is not part
                    // of the scenario and resets the toggles.
                    VPRINTF(LOW, "MCU: FAIL - bus reset during RF leg %d\n", leg);
                    total_errors++;
                    leg_armed = false;
                }
            }
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_DEV_INT_MASK);
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
            uint32_t cmd = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
            if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
                usb_handle_control_transfer();
            } else {
                usb_ep0_arm_out();
            }
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP0IN_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
        }

        // Arm leg 0 once SET_CONFIGURATION has been accepted. The host sends
        // its first leg only after enumeration; if it is early the endpoint
        // simply NAKs until armed.
        if (!leg_armed && usb_is_configured()) {
            rf_arm_leg(leg);
            leg_armed = true;
        }

        if (reg_data & DEV0_CSR_INTSTAT_EP5OUT_MASK) {
            lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP5OUT_MASK);
            if (!leg_armed) {
                VPRINTF(LOW, "MCU: FAIL - EP5 OUT interrupt with no leg armed\n");
                total_errors++;
            } else {
                rf_check_leg(leg);
                leg++;
                leg_armed = false;
                if (leg < USB_RF_NUM_LEGS) {
                    rf_arm_leg(leg);
                    leg_armed = true;
                }
            }
        }

        if (poll_count % 5000 == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] leg=%d DEVCMDSTAT=0x%x INTSTAT=0x%x EPINUSE=0x%x B0=0x%x B1=0x%x\n",
                    poll_count, leg,
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT),
                    lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT),
                    lsu_read_32(USB_DEV_EPINUSE),
                    lsu_read_32(rf_desc_addr(0u)),
                    lsu_read_32(rf_desc_addr(1u)));
        }
    }

    if (leg != USB_RF_NUM_LEGS) {
        // The most likely cause is a toggle mismatch: the device ACKed and
        // discarded the packet, so Active never cleared. Compare the last
        // "armed" line's EPTOGGLE against the PID the host sent.
        VPRINTF(LOW, "MCU: FAIL - only %d of %d RF legs completed\n", leg, USB_RF_NUM_LEGS);
        total_errors++;
    }

    if (total_errors != 0) {
        VPRINTF(LOW, "MCU: USB HS EP-info rate-feedback test - %d error(s)\n", total_errors);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    } else {
        VPRINTF(LOW, "MCU: USB HS EP-info rate-feedback test - all firmware checks passed\n");
    }

    VPRINTF(LOW, "MCU: USB HS EP-info rate-feedback test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
