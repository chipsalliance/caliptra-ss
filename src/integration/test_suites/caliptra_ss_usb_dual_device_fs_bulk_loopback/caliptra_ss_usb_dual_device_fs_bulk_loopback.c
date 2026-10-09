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
// caliptra_ss_usb_dual_device_fs_bulk_loopback - interrupt-driven dual-device
// FULL-SPEED bulk loopback.
//
// Full-speed counterpart of caliptra_ss_usb_dual_device_hs_bulk_loopback. The
// only firmware-visible difference is the device bring-up entry point: this
// test calls boot_usb_core_fs() instead of boot_usb_core_hub(). That variant is
// identical except that it sets DEVCMDSTAT bit 21 (FORCE_FULLSPEED, the legacy
// PFSC bit) before connecting, which suppresses the device-side K-chirp so the
// UTMI TX is ready for FS packet exchange immediately after bus reset. The host
// VIP for this test runs with high_speed_capable=0, so no chirp reply is ever
// driven; without FORCE_FULLSPEED the controller would burn the full chirp
// timeout (~2.2 ms) before falling back to FS and would NAK the first SETUP
// tokens. Everything else (EP list layout, interrupt topology, loopback state
// machine, 64-byte payload) is unchanged from the HS test: 64 bytes is a valid
// EP1 bulk transfer at FS (max packet 64) as well as at HS (max packet 512).
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
#define USB_EP_LIST_EP0_OUT_OFFSET    0x000u
#define USB_EP_LIST_EP0_SETUP_OFFSET  0x004u
#define USB_EP_LIST_EP0_IN_OFFSET     0x008u
#define USB_EP_LIST_EP1_OUT_OFFSET    0x010u
#define USB_EP_LIST_EP1_IN_OFFSET     0x018u

// Debug instrumentation period for the main poll loop heartbeat. Tightened
// from the original 10000 so a hang is characterized with several samples
// before the poll ceiling is reached.
#define USB_DBG_HEARTBEAT_PERIOD      2000u

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

// -----------------------------------------------------------------------------
// Debug instrumentation.
//
// usb_dbg_dump() prints, for the CURRENTLY SELECTED device, the full set of
// state that determines whether the controller can answer a host token:
//
//   EP list words (packet SRAM, MEM-base relative):
//     +0x000 EP0 OUT  : expected 0x80004005 once armed by usb_ep0_reinit()
//                       (Active | NBytes=8 | AddrOffset=0x140>>6=5).
//                       A value of 0x80000005 means Active | NBytes=0 - the
//                       controller has no room staged for the 8-byte SETUP or
//                       the OUT data stage and will NAK. usb_ep0_arm_out() in
//                       libs/usb/usb.c omits USB_EP_ENTRY_NBYTES(8), so this
//                       dump is the direct test of that hypothesis.
//     +0x004 EP0 SETUP: expected 0x00000004 (AddrOffset=0x100>>6=4, no Active;
//                       the SETUP entry is an address-only entry).
//     +0x008 EP0 IN   : Active set only while an IN response is staged.
//     +0x010 EP1 OUT / +0x018 EP1 IN: Active clears on completion.
//
//   DEVCMDSTAT with the bits that matter decoded individually, so a raw value
//   such as 0x12634E82 can be read without hand-decoding.
//
//   INTSTAT / INTEN: the ISR masks INTSTAT with INTEN before publishing to the
//   mailbox, so an event that is pending in INTSTAT but masked in INTEN never
//   reaches the foreground loop and is a common cause of a silent stall.
//
// All logging lives in THIS translation unit. Deliberately NOT adding VPRINTF
// into libs/usb/usb.c: comments there record that logging inside
// usb_read_setup_packet() and the EP0 IN arming path breaks
// tend_to_end_delay_check and the roughly 5 us IN-retry window.
// -----------------------------------------------------------------------------
static void usb_dbg_dump(const char *tag, int dev) {
    uint32_t ep0_out;
    uint32_t ep0_setup;
    uint32_t ep0_in;
    uint32_t ep1_out;
    uint32_t ep1_in;
    uint32_t cmd;
    uint32_t intstat;
    uint32_t inten;

    ep0_out   = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP0_OUT_OFFSET);
    ep0_setup = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP0_SETUP_OFFSET);
    ep0_in    = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP0_IN_OFFSET);
    ep1_out   = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET);
    ep1_in    = lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_IN_OFFSET);
    cmd       = lsu_read_32(USB_DEV_DEVCMDSTAT);
    intstat   = lsu_read_32(USB_DEV_INTSTAT);
    inten     = lsu_read_32(USB_DEV_INTEN);

    VPRINTF(LOW, "MCU: [%s] dev%d EPLIST ep0out=0x%x ep0setup=0x%x ep0in=0x%x "
            "ep1out=0x%x ep1in=0x%x\n",
            tag, dev, ep0_out, ep0_setup, ep0_in, ep1_out, ep1_in);

    // EP0 OUT NBytes is the field under suspicion; break it out explicitly.
    VPRINTF(LOW, "MCU: [%s] dev%d ep0out decode: active=%d stall=%d nbytes=%d "
            "addroff=0x%x\n",
            tag, dev,
            (ep0_out & USB_EP_ENTRY_ACTIVE) ? 1 : 0,
            (ep0_out & USB_EP_ENTRY_STALL) ? 1 : 0,
            (int)((ep0_out >> 11) & 0x7FFFu),
            (unsigned)(ep0_out & 0x7FFu));

    VPRINTF(LOW, "MCU: [%s] dev%d DEVCMDSTAT=0x%x addr=%d dev_en=%d dcon=%d "
            "setup=%d dres_c=%d dcon_c=%d dsus=%d dsus_c=%d\n",
            tag, dev, cmd,
            (int)(cmd & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK),
            (cmd & DEV0_CSR_DEVCMDSTAT_DEV_EN_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_DCON_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_DCON_C_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK) ? 1 : 0);

    // Speed / forcing bits. FORCE_FULLSPEED must read back 1 on BOTH
    // controllers in this FS test; if it is 0 the device still chirps and the
    // link will not settle at FS. SPEED reports the negotiated line rate.
    VPRINTF(LOW, "MCU: [%s] dev%d speed: force_fs=%d force_vbus=%d "
            "vbus_deb=%d speed_field=0x%x lpm_sup=%d force_needclk=%d\n",
            tag, dev,
            (cmd & DEV0_CSR_DEVCMDSTAT_FORCE_FULLSPEED_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_FORCE_VBUS_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_VBUS_DEBOUNCED_MASK) ? 1 : 0,
            (unsigned)(cmd & DEV0_CSR_DEVCMDSTAT_SPEED_MASK),
            (cmd & DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK) ? 1 : 0,
            (cmd & DEV0_CSR_DEVCMDSTAT_FORCE_NEEDCLK_MASK) ? 1 : 0);

    VPRINTF(LOW, "MCU: [%s] dev%d INTSTAT=0x%x INTEN=0x%x masked=0x%x "
            "configured=%d setup_dispatches=%d bus_resets=%d\n",
            tag, dev, intstat, inten, intstat & inten,
            (int)usb_is_configured(),
            (int)usb_legacy_ep0_get_setup_dispatch_count(),
            (int)usb_legacy_ep0_get_bus_reset_count());
}

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

    // boot_usb_core_fs() only enables DEV_INT/EP0OUT/EP0IN, and the ISR masks
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

    // Trace every batch of events the mailbox delivered for this controller.
    // This is the primary timeline: comparing these timestamps against the
    // host sequence's transfer timestamps shows whether firmware ever saw the
    // event for a token the host believes was NAK'd.
    if (usb_events != 0u)
        VPRINTF(LOW, "MCU: dev%d events=0x%x (dev_int=%d ep0out=%d ep0in=%d "
                "ep1out=%d ep1in=%d)\n",
                dev, usb_events,
                (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) ? 1 : 0,
                (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) ? 1 : 0,
                (usb_events & DEV0_CSR_INTSTAT_EP0IN_MASK) ? 1 : 0,
                (usb_events & DEV0_CSR_INTSTAT_EP1OUT_MASK) ? 1 : 0,
                (usb_events & DEV0_CSR_INTSTAT_EP1IN_MASK) ? 1 : 0);

    // Bus reset: hardware clears Active on all endpoints, so a re-arm is
    // required. usb_handle_bus_reset() restores EP0 entries; EP1 is re-armed
    // below once we are back in the enumerated state.
    usb_handle_bus_reset();

    if (usb_events & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
        uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
        if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
            usb_dbg_dump("dres_c-pre", dev);
            usb_handle_bus_reset();
            usb_dbg_dump("dres_c-post", dev);
            if (st->ep1_armed) {
                st->ep1_armed = false;
                VPRINTF(LOW, "MCU: dev%d bus reset - EP1 arm cleared\n", dev);
            }
        }
    }

    if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
        uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);
        if (cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
            // SETUP packet - decode and respond. Dump after the handler so
            // the logging does not sit between the SETUP and the response
            // arming (the EP0 IN retry window is only about 5 us).
            bool handled = usb_handle_control_transfer();
            VPRINTF(LOW, "MCU: dev%d EP0OUT -> SETUP path, handled=%d\n",
                    dev, (int)handled);
            usb_dbg_dump("setup-post", dev);
        } else {
            // Status-stage ZLP OUT for a control-read completed. Re-arm EP0
            // OUT so the next SETUP is received instead of NAK'd.
            //
            // The dump straddles this call deliberately: usb_ep0_arm_out()
            // writes the EP0 OUT entry WITHOUT an NBytes field, so comparing
            // zlp-pre against zlp-post shows whether the re-arm drops NBytes
            // from 8 to 0 and leaves the controller unable to accept the next
            // 8-byte SETUP.
            usb_dbg_dump("zlp-pre", dev);
            usb_ep0_arm_out();
            usb_dbg_dump("zlp-post", dev);
        }
    }

    // EP0 IN completion needs no action: the ISR already acknowledged it.
    if (usb_events & DEV0_CSR_INTSTAT_EP0IN_MASK)
        VPRINTF(LOW, "MCU: dev%d EP0 IN completed\n", dev);

    // Arm EP1 OUT once the device is configured (enumeration complete). This
    // is idempotent and only (re-)arms when not already armed.
    if (!st->ep1_armed && usb_is_configured()) {
        VPRINTF(LOW, "MCU: dev%d reached CONFIGURED, arming EP1 OUT\n", dev);
        usb_ep1_out_arm();
        st->ep1_armed = true;
        usb_dbg_dump("ep1-armed", dev);
    }

    // EP1 OUT completion: copy the received bytes to the EP1 IN buffer and arm
    // EP1 IN for the loopback.
    if (st->ep1_armed && !st->loopback_armed
        && (usb_events & DEV0_CSR_INTSTAT_EP1OUT_MASK)) {
        usb_dbg_dump("ep1out-done", dev);
        usb_ep1_loopback_arm_in();
        st->loopback_armed = true;
        usb_dbg_dump("ep1in-armed", dev);
    }

    // EP1 IN completion: loopback done for this device.
    if (st->loopback_armed && !st->done && usb_ep1_in_complete()) {
        st->done = true;
        VPRINTF(LOW, "MCU: dev%d EP1 bulk loopback complete\n", dev);
        usb_dbg_dump("loopback-done", dev);
    }
}

void main(void) {
    uint32_t poll_count;
    usb_dev_loopback_state_t dev_state[2] = {0};

    VPRINTF(LOW, "=================\nMCU: USB dual-device FS bulk loopback test\n=================\n\n");

    boot_mcu();

    // Bring up BOTH controllers in FS-only mode. boot_usb_core_fs() is the
    // full-speed variant of boot_usb_core_hub(): it programs the hub (HUB_EN)
    // and the active device's EP list/DEVCMDSTAT/INTEN identically, and
    // additionally sets DEVCMDSTAT.FORCE_FULLSPEED so the device does not drive
    // the K-chirp. The host VIP is configured with high_speed_capable=0, so no
    // chirp handshake can complete and the link must settle at FS.
    //
    // Program USBDC0 first, then USBDC1; the hub descriptor array is only
    // frozen once HUB_EN AND HUB_CONNECT are both set, so the second boot's
    // HUB_EN re-write is a harmless idempotent edge (HUB_CONNECT is still clear
    // at this point). FORCE_FULLSPEED is per-device, so it must be set on BOTH
    // controllers - a single boot_usb_core_fs() would leave the other
    // controller chirping.
    usb_select_device(0);
    boot_usb_core_fs();
    usb_select_device(1);
    boot_usb_core_fs();

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
            VPRINTF(LOW, "MCU: USB dual-device FS bulk loopback PASSED\n");
            break;
        }

        // Heartbeat. Prints a one-line summary plus a FULL dump of both
        // controllers so a hang is characterized without needing a waveform.
        // The period is USB_DBG_HEARTBEAT_PERIOD (2000) rather than the
        // original 10000 so several samples land before the poll ceiling.
        if (poll_count % USB_DBG_HEARTBEAT_PERIOD == 0 && poll_count > 0) {
            VPRINTF(LOW, "MCU: [poll %d] dev0 armed=%d lb=%d done=%d | "
                    "dev1 armed=%d lb=%d done=%d | intr_cnt=%d\n",
                    poll_count,
                    (int)dev_state[0].ep1_armed,
                    (int)dev_state[0].loopback_armed,
                    (int)dev_state[0].done,
                    (int)dev_state[1].ep1_armed,
                    (int)dev_state[1].loopback_armed,
                    (int)dev_state[1].done,
                    intr_count);
            usb_select_device(0);
            usb_dbg_dump("heartbeat", 0);
            usb_select_device(1);
            usb_dbg_dump("heartbeat", 1);
        }
    }

    // Firmware-side exit timeout. Reaching USB_POLL_TIMEOUT without both
    // loopbacks done is a failure, so dump the terminal state of both
    // controllers before halting. Halting here (rather than spinning) is what
    // lets the testbench's MCU-halt hook end the run instead of hanging; the
    // host-side watchdog in the sequence covers the complementary case where
    // the VIP stalls before firmware ever gets an event.
    if (!(dev_state[0].done && dev_state[1].done)) {
        VPRINTF(LOW, "MCU: USB dual-device FS bulk loopback - TIMEOUT "
                "(dev0 done=%d dev1 done=%d)\n",
                (int)dev_state[0].done, (int)dev_state[1].done);
        usb_select_device(0);
        usb_dbg_dump("timeout", 0);
        usb_select_device(1);
        usb_dbg_dump("timeout", 1);
    }

    VPRINTF(LOW, "MCU: USB dual-device FS bulk loopback test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
