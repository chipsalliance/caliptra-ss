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
// Description: USB High-Speed "VBus absent at boot" firmware for Caliptra SS.
//
// WHAT THIS TEST IS FOR
//
// Every other USB test in this suite boots with VBus already present. The VIP
// auto-attaches at 20 us (poweron_auto_attach_delay in
// caliptra_ss_usb_shared_cfg.svh) and firmware only reaches
// usb_hub_connect() at 55-70 us, so the hub's upstream connect term
//
//     hub_connect <= sync_VBusDebounced and hub_dcon_q
//     (ip_xxx_3511_hs_mem_compound_structure.a.vhdl:2103)
//
// is only ever evaluated with VBusDebounced already high. The "firmware
// enables the hub while the cable is out" ordering is therefore completely
// unexercised, even though it is the normal self-powered-device case: the SoC
// has its own supply and boots whether or not a host is plugged in.
//
// This test inverts the ordering. The companion UVM test raises
// poweron_auto_attach_delay to 150 us, which is past the measured 55-70 us
// HUB_CONNECT window, so firmware performs the whole two-phase hub bring-up
// with VBus low and only afterwards does the host appear.
//
// PHASES
//
//   Phase 0  Boot the USB core and the hub with NO VBus.
//            Checks VBUS_DEBOUNCED reads 0 before and after HUB_CONNECT, and
//            that the hub does not connect upstream on firmware's request
//            alone.
//   Phase 1  Wait for VBus to arrive (the VIP auto-attach), bounded.
//            Checks VBUS_DEBOUNCED makes a genuine 0 -> 1 transition.
//   Phase 2  Normal hub-aware enumeration, and check the link negotiated HS.
//
// WHY boot_usb_core_hub() WORKS WITH NO VBUS
//
// usb.c gates its blocking VBus wait on the topology:
//
//     if (!hub_en && !fs_en) { usb_wait_vbus_debounced(); }
//
// The hub path deliberately skips it, because in hub-enabled mode the hub -
// not the device controller - owns the upstream connect. So the hub boot path
// is already VBus-agnostic by construction and this test is what proves it.
//
// It also matters that this is the HS (not FS) variant: the FS boot path sets
// DEVCMDSTAT.FORCE_VBUS, which would make VBUS_DEBOUNCED read 1 regardless of
// the pin and mask the whole scenario. HS leaves FORCE_VBUS clear, so
// VBUS_DEBOUNCED genuinely reflects cptra_ss_usb_USB_VBus_i.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Poll budget for the whole test. The VIP raises VBus at 150 us and the first
// bus reset historically lands 165-190 us after HUB_CONNECT, so enumeration
// completes well inside this.
#define USB_POLL_TIMEOUT 60000

// Poll budget for the Phase 1 VBus wait on its own. Deliberately separate from
// USB_POLL_TIMEOUT so a stuck VBus pin is reported as its own failure instead
// of being blamed on enumeration. This replaces the unbounded
// usb_wait_vbus_debounced() helper in usb.c, which would hang the run.
#define USB_VBUS_WAIT_TIMEOUT 40000

// Each host-side hub-aware enumeration (enumerate_hub_and_usbdc0) delivers
// exactly this many EP0 control transfers to USBDC0. Same value as the other
// hub-aware tests.
#define USB_ENUM_XFER_COUNT 7

// DEVCMDSTAT.SPEED ([23:22]) is read-only negotiated-speed status. Encoding
// confirmed empirically from caliptra_nightly_regression_2026_10_24_05_31_55:
//   caliptra_ss_usb_hs_clock final DEVCMDSTAT = 0x10810A80 -> SPEED = 2
//   caliptra_ss_usb_fs_clock final DEVCMDSTAT = 0x10410E80 -> SPEED = 1
#define USB_SPEED_FULL 1u
#define USB_SPEED_HIGH 2u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Count of USBDC0 bus resets (DRES_C) observed and serviced since boot. The
// host must bus-reset the freshly attached hub before enumeration, so this
// has to advance in Phase 2 - otherwise a pass could be scored on a link that
// never actually reset.
static volatile uint32_t usb_bus_reset_count = 0;

// Service one pass of EP0 SETUP handling plus bus-reset handling on USBDC0.
// Returns 1 if a control transfer was handled on this pass, else 0.
static uint32_t usb_service_ep0_once(void) {
    uint32_t reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
    uint32_t intstat  = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT);
    uint32_t handled  = 0;

    if (intstat & DEV0_CSR_INTSTAT_DEV_INT_MASK) {
        if (reg_data & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
            usb_handle_bus_reset();
            usb_bus_reset_count++;
        }
        lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_DEV_INT_MASK);
    }

    if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
        lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
        if (reg_data & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
            if (usb_handle_control_transfer()) {
                handled = 1;
            }
        } else {
            usb_ep0_arm_out();
        }
    }

    if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK) {
        lsu_write_32(SOC_USB_COMBO_DEV0_CSR_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);
    }

    return handled;
}

static uint32_t usb_vbus_debounced(void) {
    return (lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT)
            & DEV0_CSR_DEVCMDSTAT_VBUS_DEBOUNCED_MASK) ? 1u : 0u;
}

void main(void) {
    uint32_t reg_data;
    uint32_t poll_count;
    uint32_t xfer_count;
    uint32_t speed_field;
    uint32_t bus_reset_count_before_enum;

    VPRINTF(LOW, "=================\nMCU: USB HS VBus-absent-at-boot test\n=================\n\n");

    boot_mcu();

    // ------------------------------------------------------------------
    // Phase 0a: VBus must be absent before the USB core is touched.
    //
    // This is the first check in the suite that ever observes
    // VBUS_DEBOUNCED low. If it reads 1 here the UVM side failed to defer
    // its auto-attach and the test has silently degenerated into the
    // ordinary always-VBus-present scenario, which every other test
    // already covers. Fail loudly rather than pass vacuously.
    // ------------------------------------------------------------------
    if (usb_vbus_debounced()) {
        VPRINTF(LOW, "MCU: FAIL - VBUS_DEBOUNCED already set before USB bring-up; "
                     "poweron_auto_attach_delay is too short for this test\n");
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: Phase 0a - VBUS_DEBOUNCED=0 as expected (cable out)\n");

    // ------------------------------------------------------------------
    // Phase 0b: Full two-phase hub bring-up with no VBus.
    //
    // boot_usb_core_hub() programs the HUB descriptor array, sets HUB_EN,
    // and programs USBDC0's EP list / DEVCMDSTAT / DCON. It does NOT block
    // on VBus (see the file header). usb_hub_connect() then sets
    // HUB_EN|HUB_CONNECT, which is firmware asking to connect upstream.
    // ------------------------------------------------------------------
    boot_usb_core_hub();
    usb_hub_connect();

    // ------------------------------------------------------------------
    // Phase 0c: HUB_CONNECT with no VBus must NOT connect upstream.
    //
    // hub_connect is the AND of sync_VBusDebounced and hub_dcon_q, so
    // firmware's request alone cannot put the hub on the bus. Re-check
    // VBUS_DEBOUNCED is still 0: that is the device-side half of the
    // assertion. The host-side half (the VIP link never reaching ENABLED
    // during this window) is checked by the sequence.
    //
    // Note on hub_write_lock: it is driven by HUB_EN & HUB_CONNECT with no
    // VBus term, so the descriptor flip-flop array is now frozen even
    // though the hub never appeared on the bus. That is a real design
    // property and is recorded here because nothing else documents it.
    // ------------------------------------------------------------------
    if (usb_vbus_debounced()) {
        VPRINTF(LOW, "MCU: FAIL - VBUS_DEBOUNCED set after HUB_CONNECT with no VBus\n");
        csr_write_mpmc_halt();
    }
    reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: Phase 0c - hub requested connect with VBus absent "
                 "(DEVCMDSTAT=0x%x, descriptor array now write-locked)\n", reg_data);

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();
    VPRINTF(LOW, "MCU: Caliptra core ready\n");

    // ------------------------------------------------------------------
    // Phase 1: Wait for VBus to arrive.
    //
    // Bounded, unlike usb.c's usb_wait_vbus_debounced(). Servicing EP0
    // while waiting is harmless (nothing can arrive yet) and means the
    // loop is already warm when the host does show up.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Phase 1 - waiting for VBus to arrive\n");
    for (poll_count = 0;
         poll_count < USB_VBUS_WAIT_TIMEOUT && !usb_vbus_debounced();
         poll_count++) {
        (void)usb_service_ep0_once();
    }

    if (!usb_vbus_debounced()) {
        VPRINTF(LOW, "MCU: FAIL - timeout waiting for VBus to arrive\n");
        csr_write_mpmc_halt();
    }
    reg_data = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
    VPRINTF(LOW, "MCU: Phase 1 - VBUS_DEBOUNCED went 0 -> 1 after %d polls "
                 "(DEVCMDSTAT=0x%x)\n", poll_count, reg_data);

    // ------------------------------------------------------------------
    // Phase 2: Enumerate, now that the host is actually present.
    //
    // The hub was already asking to connect, so hub_connect asserts as
    // soon as VBus debounces and the host sees an attach with no further
    // firmware action. Service EP0 until the host has completed the
    // hub-aware enumeration of USBDC0.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "MCU: Phase 2 - enumeration after late VBus\n");
    bus_reset_count_before_enum = usb_bus_reset_count;
    xfer_count = 0;
    for (poll_count = 0;
         poll_count < USB_POLL_TIMEOUT && xfer_count < USB_ENUM_XFER_COUNT;
         poll_count++) {
        if (usb_service_ep0_once()) {
            xfer_count++;
            VPRINTF(LOW, "MCU: enumeration transfer %d of %d\n",
                    xfer_count, USB_ENUM_XFER_COUNT);
        }
    }

    if (xfer_count < USB_ENUM_XFER_COUNT) {
        VPRINTF(LOW, "MCU: FAIL - enumeration timeout (got %d of %d)\n",
                xfer_count, USB_ENUM_XFER_COUNT);
        csr_write_mpmc_halt();
    }

    // A fresh attach must be followed by a host bus reset. Without this
    // check a pass could be scored on a link that somehow enumerated
    // without ever resetting.
    if (usb_bus_reset_count <= bus_reset_count_before_enum) {
        VPRINTF(LOW, "MCU: FAIL - no bus reset observed during post-VBus "
                     "enumeration (count stayed at %d)\n", usb_bus_reset_count);
        csr_write_mpmc_halt();
    }

    // ------------------------------------------------------------------
    // Phase 2b: The link must have come up at High Speed.
    //
    // Worth checking explicitly here. usb_pie's disconnect/init path
    // asserts set_dev_fs, discarding any negotiated speed, so a device
    // that attaches late is exactly the case where a missed chirp would
    // leave the link stuck at FS. Nothing else in the suite asserts the
    // negotiated speed after a late or repeated attach.
    // ------------------------------------------------------------------
    reg_data    = lsu_read_32(SOC_USB_COMBO_DEV0_CSR_DEVCMDSTAT);
    speed_field = (reg_data & DEV0_CSR_DEVCMDSTAT_SPEED_MASK)
                  >> DEV0_CSR_DEVCMDSTAT_SPEED_LOW;

    if (speed_field != USB_SPEED_HIGH) {
        VPRINTF(LOW, "MCU: FAIL - link negotiated SPEED=%d, expected HS (%d). "
                     "DEVCMDSTAT=0x%x\n",
                speed_field, USB_SPEED_HIGH, reg_data);
        csr_write_mpmc_halt();
    }
    VPRINTF(LOW, "MCU: Phase 2b - link negotiated HS (SPEED=%d)\n", speed_field);

    VPRINTF(LOW, "MCU: USB HS VBus-absent-at-boot test PASSED "
                 "(%d transfers, %d bus resets)\n",
            xfer_count, usb_bus_reset_count);

    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
