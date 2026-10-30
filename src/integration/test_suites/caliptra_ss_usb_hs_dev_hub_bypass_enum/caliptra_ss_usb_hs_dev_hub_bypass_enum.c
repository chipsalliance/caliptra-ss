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
// Description: USB High-Speed HUB BYPASS enumeration firmware for Caliptra SS.
//
// WHAT THIS TEST IS FOR
//
// hub_enable is not a strap on this part. USB_EnableHub is tied 1'b0 at top
// level (caliptra_ss_top.sv), so hub_enable_q inside the compound IP follows
// the firmware-written HUB_CTRL.HUB_EN bit (ep0_mem(C_HUB_CS)(0) in
// usb_ep0_hub_descr.m.vhdl). Leaving HUB_EN clear selects the "hub bypass"
// topology, in which four muxes in
// ip_xxx_3511_hs_mem_compound_structure.a.vhdl take their else-leg at once:
//
//   usb_dev_connect         <= hub_connect when hub_enable_q = '1'
//                              else dev0_usbreg_dev_connect;
//   usbreg_deviceenabled(0) <= hub_connect when hub_enable_q = '1' else '0';
//   usbreg_deviceenabled(1) <= hub_port_enable(0) and dev0_usbreg_deviceenabled
//                              when hub_enable_q = '1'
//                              else dev0_usbreg_deviceenabled;
//   upd_dev0_portreset      <= dev0_portreset when hub_enable_q = '1'
//                              else sync_busreset;
//
// So device0 owns the upstream connect, the hub is not a bus participant, the
// device enable is not gated by any hub port enable, and the device port reset
// comes straight from the upstream bus reset. Every other enumerating USB test
// in the suite sets HUB_EN, so these four else-legs are only covered here.
//
// WHAT THE FIRMWARE HAS TO DO: ALMOST NOTHING
//
// The hub-bypass path is already implemented in the shared library. usb.c's
// entry point is boot_usb_core(fs_en, hub_en), and the whole topology choice is
// that second argument:
//
//   if (hub_en) { usb_hub_init_and_connect(); }        // writes HUB_EN
//   if (!hub_en && !fs_en) { usb_wait_vbus_debounced(); }
//   if (hub_en) { reg_data |= FORCE_NEEDCLK; }
//
// mcu_cptra_init_d() forwards args.usb_hub_en / args.usb_fs_en to it, and
// caliptra_ss_lib.h defaults both to false. So requesting
// .cfg_boot_usb_core=true and NOT setting .usb_hub_en is exactly the bypass
// configuration: HUB_EN is never written, usb_hub_connect() is never called,
// and FORCE_NEEDCLK stays clear. The usb_hub_en argument is passed explicitly
// as false below anyway, so the intent is visible at the call site rather than
// resting on a struct default that a future edit could change.
//
// NOTE ON THE BLOCKING VBUS WAIT
//
// The bypass leg is the ONE path in boot_usb_core() that calls the unbounded
// usb_wait_vbus_debounced() before asserting DCON, and it is correct that it
// does: with the hub out of the picture nothing else gates the upstream
// connect, so the device must not pull up before VBus is debounced. It cannot
// hang in this test because the VIP auto-attaches at 20 us
// (poweron_auto_attach_delay in caliptra_ss_usb_shared_cfg.svh) and the MCU
// only reaches USB bring-up at ~32 us, i.e. VBus is already high on arrival.
// Phase 0 below records the observed VBUS_DEBOUNCED value so a future change
// to the attach timing shows up as a log line rather than a silent hang.
// A deliberately-late-VBus scenario belongs to
// caliptra_ss_usb_hs_dev_vbus_absent_boot, which is hub mode precisely because
// hub mode skips this wait.
//
// HS, NOT FS
//
// Full-Speed bring-up sets DEVCMDSTAT.FORCE_VBUS and HUB_CTRL.FORCE_FULLSPEED
// (the latter via usb_hub_force_fullspeed(), which writes HUB_CTRL). Writing
// HUB_CTRL at all in a test whose premise is "HUB_CTRL.HUB_EN stays 0" muddies
// the scenario, and FORCE_VBUS would additionally mask the VBUS_DEBOUNCED
// observation above. HS leaves both alone, so the HS variant is the clean one.
//
// CHECKS (all failures reported through the total_errors pattern)
//
//   Phase 0  HUB_CTRL reads back with HUB_EN = 0 and HUB_CONNECT = 0 after the
//            USB core is fully booted. This is the direct assertion that the
//            bypass topology is in force and nothing wrote HUB_EN behind our
//            back.
//   Phase 1  DEVCMDSTAT has DEV_EN and DCON set (device0 is enabled and is
//            itself requesting the upstream connect) and FORCE_NEEDCLK clear
//            (that bit is a hub-mode-only workaround).
//   Phase 2  Serve the host enumeration and confirm all 7 control transfers
//            were handled.
//   Phase 3  At least one bus reset (DRES_C) was observed. In bypass topology
//            that reset arrives through the sync_busreset leg of
//            upd_dev0_portreset rather than from the hub's per-port reset
//            logic, so it is the most direct firmware-visible evidence that
//            the reparented reset path works.
//   Phase 4  DEVCMDSTAT.DEV_ADDR == 1 and SPEED == HS. The host assigns
//            address 1 here, not the address 2 of the hub-mode tests, because
//            there is no hub occupying address 1.
//
// VERDICT
//
// Errors are counted and reported with SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL),
// which is the only thing that actually fails a run - a VPRINTF saying "FAIL"
// does not (see claude_md/16_usb_silent_fail_verdict_gap.md). TB_CMD_TEST_PASS
// is deliberately NOT sent: it $finishes the simulation before the UVM
// final_phase runs, which would discard the host-side sequence checks.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Poll budget for the enumeration event loop. The flat bypass enumeration is
// shorter than the hub-aware one (no hub enumeration, no port bring-up), so
// the budget used by caliptra_ss_usb_init is more than sufficient.
#define USB_POLL_TIMEOUT 20000

// Control transfers issued by caliptra_ss_usb_hs_dev_hub_bypass_enum_sequence:
// GET_DESCRIPTOR(addr0), GET_STATUS(addr0), SET_ADDRESS(1),
// GET_DESCRIPTOR(addr1), GET_CONFIGURATION(addr1), SET_CONFIGURATION(1),
// GET_CONFIGURATION(addr1) verify.
//
// All seven land on USBDC0. This is the same count as the hub-mode tests, but
// for a different reason: there the hub answers its own enumeration in
// hardware and only the step-C transfers reach the device, whereas here every
// transfer of the whole enumeration is served by device0 firmware.
//
// Note on the GET_STATUS reply, because it is easy to get wrong: the shared
// usb.c handler hardcodes bit[0] Self-Powered to 1, so recipient=device
// GET_STATUS returns 0x0001 here (0x0003 after a SET_FEATURE(REMOTE_WAKEUP),
// which this test never issues). The host sequence asserts 0x0001. This
// firmware does not inspect the status word itself; the value is recorded here
// only so the two sides cannot drift.
#define USB_EXPECTED_TRANSFERS 7

// DEVCMDSTAT.SPEED ([23:22]) read-only negotiated-speed status. Encoding taken
// from usb_subcmp_pkg.p.vhdl and confirmed empirically (see
// claude_md/31_usb_vbus_absent_boot.md section 5).
#define USB_SPEED_FULL 1u
#define USB_SPEED_HIGH 2u

// Address the host assigns to USBDC0 in bypass topology. Only one device is on
// the bus, so it gets address 1. Hub-mode tests use 2 because the hub already
// holds 1 - keeping this as a named constant stops that difference from being
// read as a typo.
#define USB_BYPASS_DEV_ADDRESS 1u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void main(void) {
    uint32_t total_errors = 0;
    uint32_t hub_ctrl;
    uint32_t devcmdstat;
    uint32_t vbus_debounced;
    uint32_t transfers_handled;
    uint32_t bus_reset_count;
    uint32_t dev_addr;
    uint32_t speed_field;

    VPRINTF(LOW, "==========================================\n"
                 "MCU: USB HS hub-bypass enumeration test\n"
                 "==========================================\n\n");

    // ------------------------------------------------------------------
    // Bring up the MCU and the USB device controller in BYPASS topology.
    //
    // usb_hub_en = false is the whole point of this test: it makes
    // boot_usb_core() skip usb_hub_init_and_connect(), so HUB_CTRL.HUB_EN is
    // never written and hub_enable_q stays 0. usb_hub_connect() is likewise
    // never called from here - in bypass topology there is no hub to connect,
    // and calling it would set HUB_EN and silently convert this into an
    // ordinary hub-mode test.
    //
    // Note this call blocks inside usb_wait_vbus_debounced() until VBus is
    // debounced (bypass is the only topology that waits); see the file header
    // for why that cannot hang here.
    // ------------------------------------------------------------------
    mcu_cptra_init_d(
        .cfg_enable_cptra_mbox_user_init=true,
        .cfg_cptra_fuse=true,
        .cfg_cptra_wdt=true,
        .cptra_wdt_cfg_0=1u,
        .cfg_boot_usb_core=true,
        .usb_hub_en=false,
        .usb_fs_en=false);

    mcu_cptra_poll_mb_ready();

    usb_dump_state("post-boot (hub bypass)");

    // ------------------------------------------------------------------
    // Phase 0: the hub must be disabled and not connected.
    //
    // This is the assertion that the topology under test is actually in
    // force. If HUB_EN reads back set, something wrote HUB_CTRL (a stray
    // usb_hub_connect(), a usb_hub_force_fullspeed() from an FS path, or a
    // future change to the boot_usb_core() argument plumbing) and the run has
    // silently degenerated into the hub-mode scenario that every other test
    // already covers. Fail loudly rather than pass vacuously.
    //
    // HUB_EN is checked against USBHUB_CTRL_HUB_EN_MASK, which covers BOTH
    // bit 0 (the position the RTL actually samples) and bit 7 (the legacy
    // position the firmware also writes) - see the mask definition in usb.h.
    // Any of those bits being set means the hub was enabled.
    // ------------------------------------------------------------------
    hub_ctrl = lsu_read_32(USB_HUB_CTRL);

    if ((hub_ctrl & USBHUB_CTRL_HUB_EN_MASK) != 0u) {
        VPRINTF(LOW, "MCU: FAIL - HUB_EN is set (HUB_CTRL=0x%x); the hub is "
                     "enabled, so this is not the bypass topology\n", hub_ctrl);
        total_errors++;
    }
    if ((hub_ctrl & USBHUB_CTRL_HUB_CONNECT_MASK) != 0u) {
        VPRINTF(LOW, "MCU: FAIL - HUB_CONNECT is set (HUB_CTRL=0x%x); the hub "
                     "is requesting an upstream connect in bypass topology\n",
                hub_ctrl);
        total_errors++;
    }
    if (total_errors == 0u) {
        VPRINTF(LOW, "MCU: Phase 0 - hub disabled and disconnected as expected "
                     "(HUB_CTRL=0x%x), device0 is directly on the bus\n",
                hub_ctrl);
    }

    // ------------------------------------------------------------------
    // Phase 1: device0 must own the upstream connect by itself.
    //
    // DEV_EN plus DCON is device0 asking to be on the bus. With hub_enable_q
    // at 0 that request reaches the upstream port through the else-leg of the
    // usb_dev_connect mux with nothing else in the way - no hub_connect term,
    // no hub_port_enable gate.
    //
    // FORCE_NEEDCLK must be clear. boot_usb_core() only sets it when hub_en is
    // true (it keeps the UTMI clock running for the hub), so a set bit here
    // would be a second, independent indication that the hub path ran.
    //
    // VBUS_DEBOUNCED is logged rather than checked: it is an input condition
    // of the test, not a property of the DUT. It is already implied by the
    // boot having returned at all, since the bypass leg of boot_usb_core()
    // blocks until it is high.
    // ------------------------------------------------------------------
    devcmdstat     = lsu_read_32(USB_DEV_DEVCMDSTAT);
    vbus_debounced = (devcmdstat & DEV0_CSR_DEVCMDSTAT_VBUS_DEBOUNCED_MASK)
                     ? 1u : 0u;

    if ((devcmdstat & DEV0_CSR_DEVCMDSTAT_DEV_EN_MASK) == 0u) {
        VPRINTF(LOW, "MCU: FAIL - DEV_EN clear after boot (DEVCMDSTAT=0x%x)\n",
                devcmdstat);
        total_errors++;
    }
    if ((devcmdstat & DEV0_CSR_DEVCMDSTAT_DCON_MASK) == 0u) {
        VPRINTF(LOW, "MCU: FAIL - DCON clear after boot (DEVCMDSTAT=0x%x); in "
                     "bypass topology device0 itself must request the upstream "
                     "connect\n", devcmdstat);
        total_errors++;
    }
    if ((devcmdstat & DEV0_CSR_DEVCMDSTAT_FORCE_NEEDCLK_MASK) != 0u) {
        VPRINTF(LOW, "MCU: FAIL - FORCE_NEEDCLK is set (DEVCMDSTAT=0x%x); that "
                     "bit is only set by the hub-mode boot path\n", devcmdstat);
        total_errors++;
    }
    VPRINTF(LOW, "MCU: Phase 1 - device0 enabled and connected "
                 "(DEVCMDSTAT=0x%x, VBUS_DEBOUNCED=%d)\n",
            devcmdstat, vbus_debounced);

    VPRINTF(LOW, "MCU: Caliptra core ready, entering USB event loop "
                 "(expecting %d control transfers)\n", USB_EXPECTED_TRANSFERS);

    // ------------------------------------------------------------------
    // Phase 2: serve the host enumeration.
    //
    // usb_event_loop() handles the bus reset (DRES_C), EP0 SETUP dispatch and
    // the EP0 OUT re-arm on the status-stage ZLP. Nothing in it is
    // hub-specific, which is why the bypass topology needs no firmware
    // enumeration code of its own.
    // ------------------------------------------------------------------
    transfers_handled = usb_event_loop(USB_POLL_TIMEOUT, USB_EXPECTED_TRANSFERS);

    usb_dump_state("final (hub bypass)");

    if (transfers_handled < USB_EXPECTED_TRANSFERS) {
        VPRINTF(LOW, "MCU: FAIL - enumeration incomplete, handled %d of %d "
                     "control transfers\n",
                transfers_handled, USB_EXPECTED_TRANSFERS);
        total_errors++;
    } else {
        VPRINTF(LOW, "MCU: Phase 2 - handled all %d enumeration control "
                     "transfers\n", transfers_handled);
    }

    // ------------------------------------------------------------------
    // Phase 3: a bus reset must have been seen.
    //
    // The host resets the device before enumerating it. In bypass topology
    // that reset reaches device0 through
    //   upd_dev0_portreset <= sync_busreset   (hub_enable_q = '0' leg)
    // instead of the hub's dev0_portreset, so observing DRES_C is the most
    // direct firmware-visible evidence that the reparented reset path works.
    // Without this check an enumeration that somehow completed with no reset
    // at all would still score a pass.
    //
    // usb_legacy_ep0_get_bus_reset_count() is the shared library's own
    // counter, incremented inside usb_handle_bus_reset() which
    // usb_event_loop() calls on every DRES_C - so it counts the resets this
    // run actually serviced, not a register snapshot. The "legacy_ep0" prefix
    // is historical (the accessor was added for the OCP snapshot handshake);
    // the counter itself is the generic one in usb.c and is valid for any
    // test that drives the event loop.
    // ------------------------------------------------------------------
    bus_reset_count = usb_legacy_ep0_get_bus_reset_count();

    if (bus_reset_count == 0u) {
        VPRINTF(LOW, "MCU: FAIL - no bus reset (DRES_C) observed during "
                     "enumeration; the upd_dev0_portreset bypass leg did not "
                     "deliver the host reset\n");
        total_errors++;
    } else {
        VPRINTF(LOW, "MCU: Phase 3 - %d bus reset(s) observed via the bypass "
                     "reset path\n", bus_reset_count);
    }

    // ------------------------------------------------------------------
    // Phase 4: committed address and negotiated speed.
    //
    // DEV_ADDR must be 1: in bypass topology USBDC0 is the only device on the
    // bus and takes the first address the host hands out. The hub-mode tests
    // see 2 here because the hub holds 1.
    //
    // SPEED must be HS. The chirp handshake runs off the reparented reset net
    // in this topology, and usb_pie's init path asserts set_dev_fs, so a
    // missed chirp would leave the link at Full Speed with the enumeration
    // still completing successfully. Checking the speed is what closes that.
    // ------------------------------------------------------------------
    devcmdstat  = lsu_read_32(USB_DEV_DEVCMDSTAT);
    dev_addr    = devcmdstat & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK;
    speed_field = (devcmdstat & DEV0_CSR_DEVCMDSTAT_SPEED_MASK)
                  >> DEV0_CSR_DEVCMDSTAT_SPEED_LOW;

    if (dev_addr != USB_BYPASS_DEV_ADDRESS) {
        VPRINTF(LOW, "MCU: FAIL - DEV_ADDR=%d, expected %d "
                     "(DEVCMDSTAT=0x%x)\n",
                dev_addr, USB_BYPASS_DEV_ADDRESS, devcmdstat);
        total_errors++;
    } else {
        VPRINTF(LOW, "MCU: Phase 4 - device0 committed address %d\n", dev_addr);
    }

    if (speed_field != USB_SPEED_HIGH) {
        VPRINTF(LOW, "MCU: FAIL - link negotiated SPEED=%d, expected HS (%d). "
                     "DEVCMDSTAT=0x%x\n",
                speed_field, USB_SPEED_HIGH, devcmdstat);
        total_errors++;
    } else {
        VPRINTF(LOW, "MCU: Phase 4 - link negotiated HS (SPEED=%d)\n",
                speed_field);
    }

    // ------------------------------------------------------------------
    // Verdict. Only SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL) actually fails a run;
    // a VPRINTF that says FAIL does not. TB_CMD_TEST_PASS is never sent - it
    // $finishes before the UVM final_phase and would throw away the host-side
    // checks. On success the firmware just halts and lets the UVM verdict
    // stand.
    // ------------------------------------------------------------------
    if (total_errors != 0u) {
        VPRINTF(LOW, "MCU: USB HS hub-bypass enumeration test FAILED "
                     "(%d error(s))\n", total_errors);
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    } else {
        VPRINTF(LOW, "MCU: USB HS hub-bypass enumeration test PASSED "
                     "(%d transfers, address %d, HS, hub never enabled)\n",
                transfers_handled, dev_addr);
    }

    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
