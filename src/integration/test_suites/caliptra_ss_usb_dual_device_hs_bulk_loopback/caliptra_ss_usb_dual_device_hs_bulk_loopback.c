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
// -----------------------------------------------------------------------------
// caliptra_ss_usb_dual_device_hs_bulk_loopback - interrupt-driven dual-device
// bulk loopback.
//
// This test exercises BOTH embedded device controllers of the compound USB IP
// (IP_3511) at the same time, behind the on-chip 2-port hub:
//   - USBDC0 (device0): CSR 0x2000_0000, MEM 0x3000_0000, PIC vector 3.
//   - USBDC1 (device1): CSR 0x2000_2000, MEM 0x3001_0000, PIC vector 6.
//
// USBDC0's IRQ is wired to cptra_ss_mcu_ext_int[3] in RTL. USBDC1's IRQ is NOT
// routed to the PIC in caliptra_ss_top.sv; instead the testbench loops the top
// level output cptra_ss_usb_dev1_irq_o back onto cptra_ss_mcu_ext_int[6], gated
// by the compile define USB_HUB_COMPOUND_DEV1_IRQ (Option A: no RTL change).
// That define must be passed BOTH to the RTL compile (for the TB loopback) and
// to this firmware's BUILD_CFLAGS (so init_usb_interrupts() enables vector 6
// and mcu_isr.h compiles in service_usb_dev1_intr()).
//
// Scenario (interrupt-driven, run in parallel on both controllers):
//   1. Bring up the hub once, then program BOTH USBDC0 and USBDC1 EP lists.
//   2. Enable PIC vectors 3 (dev0) and 6 (dev1) via init_usb_interrupts().
//   3. The host enumerates the hub, brings up downstream ports 1 and 2, and
//      enumerates USBDC0 (addr 2 on port 1) and USBDC1 (addr 3 on port 2).
//      The two controllers share one USB bus so they must take distinct bus
//      addresses; the controller firmware is address-agnostic (the host-side
//      SET_ADDRESS latches the value in each controller's hardware).
//      Firmware services EP0 SETUP/control transfers for each controller from
//      the ISR mailbox (mcu_intr_rcv.usb for dev0, mcu_intr_rcv.usb_dev1 for
//      dev1), retargeting the shared USB library per device with
//      usb_select_device().
//   4. Each controller performs an EP1 64-byte bulk OUT -> IN loopback: on the
//      EP1 OUT completion interrupt, firmware copies the 64 received bytes from
//      the EP1 OUT buffer (MEM+0x200) to the EP1 IN buffer (MEM+0x240) and arms
//      EP1 IN. The loopback for a device is DONE once its EP1 IN entry's Active
//      bit clears (hardware transmitted the data to the host).
//   5. The test PASSES once BOTH controllers have completed their EP1 loopback.
//
// The two PIC vectors are configured at EQUAL priority (both 7, see
// caliptra_ss_defines.h), so dev0 (vec3) and dev1 (vec6) interrupts serialize
// rather than preempt one another.
// -----------------------------------------------------------------------------

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"
// Including mcu_isr.h is what makes the build system compile and link
// mcu_isr.o for this test (see tools/scripts/Makefile). With
// USB_HUB_COMPOUND_DEV1_IRQ defined it also compiles in service_usb_dev1_intr()
// and makes init_usb_interrupts() enable PIC vector 6 for USBDC1.
#include "mcu_isr.h"

// -----------------------------------------------------------------------------
// Runtime device retargeting for THIS translation unit.
//
// usb.h resolves the device-neutral USB_DEV_* register macros and
// USB_DMA_BASE_ADDR / USB_DEV_DMA_BASE_ADDR against the COMPILE-TIME base
// selected by USB_DEV_SEL (default 0 = USBDC0). usb.c re-points those same
// macros at usb_select_device()'s RUNTIME choice, but that #undef/#define is
// scoped to usb.c's translation unit only. The functions in THIS file
// (usb_ep1_out_arm, usb_ep1_loopback_arm_in, usb_ep1_in_complete and the SETUP
// decode in usb_service_device) access USB_DEV_* directly, so without the same
// retargeting here they would always hit USBDC0's aperture even while servicing
// USBDC1 - which is why USBDC1 (dev1) never had its EP0 SETUP decoded, NAK'd its
// first SETUP and timed out.
//
// Re-apply usb.c's exact trick: re-define the two base macros in terms of the
// runtime accessors usb_active_dev_csr_base() / usb_active_dev_mem_base()
// (exported from usb.c). Every derived macro in usb.h (USB_DEV_DEVCMDSTAT,
// USB_DEV_INTEN, USB_DEV_INTSTAT, USB_DMA_BASE_ADDR, USB_DEV_DMA_BASE_ADDR,
// USB_EP_ENTRY_ABS_ADDR, ...) is expanded at its USE site, so re-pointing the
// bases makes all of them follow usb_select_device() in this file too. For a
// single-device build (no usb_select_device() call) the accessors return the
// USB_DEV_SEL base, so behaviour is unchanged.
#undef USB_DEV_CSR_BASE_ADDR
#undef USB_DEV_MEM_BASE_ADDR
#define USB_DEV_CSR_BASE_ADDR  usb_active_dev_csr_base()
#define USB_DEV_MEM_BASE_ADDR  usb_active_dev_mem_base()

// Poll loop ceiling. Sized to comfortably outlast dual enumeration + two bulk
// loopbacks. Each iteration is only a few DCCM/CSR accesses.
#define USB_POLL_TIMEOUT              200000


// EP1 OUT / IN data buffers in each controller's packet SRAM. EP0 uses
// 0x000-0x1FF, so EP1 buffers are placed after it. Both controllers use the
// same offsets inside their own MEM aperture.
#define USB_SRAM_EP1_OUT_BUF_OFFSET   0x200u
#define USB_SRAM_EP1_IN_BUF_OFFSET    0x240u

// EP command/status list byte offsets (NXP IP_3511 Integration Guide s4.2.3).
#define USB_EP_LIST_EP1_OUT_OFFSET    0x010u
#define USB_EP_LIST_EP1_IN_OFFSET     0x018u

// 64-byte bulk loopback (HS/FS EP1 bulk). Matches the host sequence's
// 64-byte OUT then 64-byte IN.
#define USB_BULK_LOOPBACK_BYTES       64u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

// Storage for the symbols the ISR library declares extern.
volatile uint32_t intr_count;
volatile mcu_intr_received_s mcu_intr_rcv = {0};

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Per-device loopback progress. Index 0 = USBDC0, 1 = USBDC1.
typedef struct {
    bool ep1_armed;      // EP1 OUT armed and EP1OUT interrupt enabled
    bool loopback_armed; // EP1 OUT data copied to EP1 IN and EP1 IN armed
    bool done;           // EP1 IN transfer completed (Active cleared)
} usb_dev_loopback_state_t;

// Arm EP1 OUT for the currently selected device and enable its EP1OUT
// interrupt so the EP1 OUT completion is published to the ISR mailbox.
// usb_select_device() must already have selected the target device, so the
// USB_DEV_* aliases resolve to that controller's aperture.
static void usb_ep1_out_arm(void) {
    uint32_t ep1_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_NBYTES(USB_BULK_LOOPBACK_BYTES)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                             + USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, ep1_out);

    // boot_usb_core_hub() only enables DEV_INT/EP0OUT/EP0IN, and the ISR masks
    // INTSTAT with INTEN, so the EP1 OUT completion would never reach the
    // mailbox without enabling the EP1OUT interrupt here.
    lsu_write_32(USB_DEV_INTEN,
                 lsu_read_32(USB_DEV_INTEN) | DEV0_CSR_INTSTAT_EP1OUT_MASK);

    VPRINTF(LOW, "MCU: dev%d EP1 OUT armed for %d bytes\n",
            usb_get_active_device(), USB_BULK_LOOPBACK_BYTES);
}

// On an EP1 OUT completion for the selected device, copy the 64 received bytes
// from the EP1 OUT buffer to the EP1 IN buffer and arm EP1 IN to send them back.
static void usb_ep1_loopback_arm_in(void) {
    uint32_t i;
    uint32_t rx_word;
    uint32_t ep1_in;

    for (i = 0; i < USB_BULK_LOOPBACK_BYTES; i += 4) {
        rx_word = lsu_read_32(USB_DEV_DMA_BASE_ADDR
                              + USB_SRAM_EP1_OUT_BUF_OFFSET + i);
        lsu_write_32(USB_DEV_DMA_BASE_ADDR
                     + USB_SRAM_EP1_IN_BUF_OFFSET + i, rx_word);
    }

    ep1_in = USB_EP_ENTRY_ACTIVE
           | USB_EP_ENTRY_NBYTES(USB_BULK_LOOPBACK_BYTES)
           | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                   + USB_SRAM_EP1_IN_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_IN_OFFSET, ep1_in);

    VPRINTF(LOW, "MCU: dev%d EP1 IN armed (loopback)\n", usb_get_active_device());
}

// Returns true once the selected device's EP1 IN transfer has completed, i.e.
// hardware cleared the Active bit on the EP1 IN command/status entry.
static bool usb_ep1_in_complete(void) {
    return (lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_IN_OFFSET)
            & USB_EP_ENTRY_ACTIVE) == 0u;
}

// Drain the ISR mailbox and advance the loopback state machine for one device.
// dev selects USBDC0 (0) or USBDC1 (1); usb_events is the snapshot of the
// matching mailbox field. The ISR has already W1C-acknowledged INTSTAT, so the
// foreground must not touch INTSTAT itself. EP1 IN completion is detected by
// polling the EP list Active bit (not INTSTAT), matching the polling loopback
// reference.
static void usb_service_device(int dev, uint32_t usb_events,
                               usb_dev_loopback_state_t *st) {
    usb_select_device(dev);

    // Bus reset: hardware clears Active on all endpoints, so a re-arm is
    // required. usb_handle_bus_reset() restores EP0 entries; EP1 is re-armed
    // below once we are back in the enumerated state.
    usb_handle_bus_reset();

    if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
        uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
        if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
            usb_handle_bus_reset();
            if (st->ep1_armed) {
                st->ep1_armed = false;
                VPRINTF(LOW, "MCU: dev%d bus reset - EP1 arm cleared\n", dev);
            }
        }
    }

    if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
        uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
        if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
            // SETUP packet - decode and respond.
            usb_handle_control_transfer();
        } else {
            // Status-stage ZLP OUT for a control-read completed. Re-arm EP0
            // OUT so the next SETUP is received instead of NAK'd.
            usb_ep0_arm_out();
        }
    }

    // EP0 IN completion needs no action: the ISR already acknowledged it.

    // Arm EP1 OUT once the device is configured (enumeration complete). This
    // is idempotent and only (re-)arms when not already armed.
    if (!st->ep1_armed && usb_is_configured()) {
        usb_ep1_out_arm();
        st->ep1_armed = true;
    }

    // EP1 OUT completion: copy the received bytes to the EP1 IN buffer and arm
    // EP1 IN for the loopback.
    if (st->ep1_armed && !st->loopback_armed
        && (usb_events & DEV0_CSR_INTSTAT_EP1OUT_MASK)) {
        usb_ep1_loopback_arm_in();
        st->loopback_armed = true;
    }

    // EP1 IN completion: loopback done for this device.
    if (st->loopback_armed && !st->done && usb_ep1_in_complete()) {
        st->done = true;
        VPRINTF(LOW, "MCU: dev%d EP1 bulk loopback complete\n", dev);
    }
}

void main(void) {
    uint32_t poll_count;
    usb_dev_loopback_state_t dev_state[2] = {0};

    VPRINTF(LOW, "=================\nMCU: USB dual-device HS bulk loopback test\n=================\n\n");

    boot_mcu();

    // Bring up BOTH controllers. boot_usb_core_hub() programs the hub (HUB_EN)
    // and the active device's EP list/DEVCMDSTAT/INTEN. Program USBDC0 first,
    // then USBDC1; the hub descriptor array is only frozen once HUB_EN AND
    // HUB_CONNECT are both set, so the second boot's HUB_EN re-write is a
    // harmless idempotent edge (HUB_CONNECT is still clear at this point).
    usb_select_device(0);
    boot_usb_core_hub();
    usb_select_device(1);
    boot_usb_core_hub();

    // Enable PIC vectors 3 (USBDC0) and 6 (USBDC1). With
    // USB_HUB_COMPOUND_DEV1_IRQ defined, init_usb_interrupts() enables both at
    // equal priority so the two controllers serialize rather than preempt.
    intr_count = 0;
    init_usb_interrupts();

    // Connect the hub upstream now that both controllers are fully programmed.
    // The host begins enumerating the hub and its downstream ports after this.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering dual-device USB event loop\n");

    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        uint32_t ev0;
        uint32_t ev1;

        // Snapshot then clear by complement so bits the ISR sets while we are
        // handling this batch are not lost.
        ev0 = mcu_intr_rcv.usb;
        mcu_intr_rcv.usb &= ~ev0;
        ev1 = mcu_intr_rcv.usb_dev1;
        mcu_intr_rcv.usb_dev1 &= ~ev1;

        // Service USBDC0 (vector 3) and USBDC1 (vector 6) in parallel.
        usb_service_device(0, ev0, &dev_state[0]);
        usb_service_device(1, ev1, &dev_state[1]);

        if (dev_state[0].done && dev_state[1].done) {
            VPRINTF(LOW, "MCU: USB dual-device HS bulk loopback PASSED\n");
            break;
        }

        if (poll_count % 10000 == 0 && poll_count > 0) {
            usb_select_device(0);
            VPRINTF(LOW, "MCU: [poll %d] dev0 armed=%d lb=%d done=%d "
                    "DEVCMDSTAT=0x%x | ",
                    poll_count, (int)dev_state[0].ep1_armed,
                    (int)dev_state[0].loopback_armed, (int)dev_state[0].done,
                    lsu_read_32(USB_DEV_DEVCMDSTAT));
            usb_select_device(1);
            VPRINTF(LOW, "dev1 armed=%d lb=%d done=%d DEVCMDSTAT=0x%x intr_cnt=%d\n",
                    (int)dev_state[1].ep1_armed, (int)dev_state[1].loopback_armed,
                    (int)dev_state[1].done, lsu_read_32(USB_DEV_DEVCMDSTAT),
                    intr_count);
        }
    }

    if (!(dev_state[0].done && dev_state[1].done))
        VPRINTF(LOW, "MCU: USB dual-device HS bulk loopback - TIMEOUT "
                "(dev0 done=%d dev1 done=%d)\n",
                (int)dev_state[0].done, (int)dev_state[1].done);

    VPRINTF(LOW, "MCU: USB dual-device HS bulk loopback test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
