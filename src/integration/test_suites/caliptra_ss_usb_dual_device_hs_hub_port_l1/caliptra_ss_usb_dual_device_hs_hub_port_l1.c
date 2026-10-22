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

// Description: MCU firmware for the PER-PORT hub L1 test. Boots BOTH embedded
// device controllers behind the on-chip 2-port hub so that the host can drive
// SetAndTestPortFeature(PORT_L1) at port 1 and port 2 independently and see
// that each one affects only its own controller.
//
// WHY A DUAL-DEVICE IMAGE IS REQUIRED HERE
//
// The hub resolves the PORT_L1 response from PER-PORT inputs that are wired to
// the DEVICE CSRs, not to the hub register (see
// ip_xxx_3511_hs_mem_compound_structure.a.vhdl):
//
//   hub_lpm_sup(0)          <= dev0_lpm_sup       (DEV0 DEVCMDSTAT[11] LPM_SUP)
//   hub_lpm_data_pending(0) <= dev0_lpm_nyet      (DEV0 LPM[8]  DATA_PENDING)
//   hub_port_lpm_hird_sw(0) <= dev0_lpm_hird_sw   (DEV0 LPM[7:4] HIRD_SW)
//   hub_lpm_sup(1)          <= dev1_lpm_sup       (DEV1, same fields)
//   ...
//
// so port 2 can only answer SUCCESS if USBDC1 is actually booted and its
// LPM_SUP is set. A single-device image would leave port 2's inputs at their
// unprogrammed values and the port-2 leg of the test would degrade into a
// refusal rather than a real per-port L1 entry.
//
// Conversely the L1 level reaches the device through:
//
//   devN_lpm_suspend <= (sync_lpm_suspend and hub_port_enable(N)) or hub_port_l1(N)
//
// which is per-port. That is what makes the ISOLATION claim observable from
// firmware: a PORT_L1 on port 1 must raise DEVCMDSTAT.LPM_SUS on USBDC0 ONLY,
// and leave USBDC1 untouched, and vice versa. Those cross-checks are the point
// of this test.
//
// RESPONSE STEERING
//
// Which of the three answers the host sees is decided HERE, by this firmware,
// before the request is ever sent - because hub_l1_status resolves it from the
// per-port device CSRs listed above:
//
//   0x30 STALL-code  if hub_lpm_sup(port) = 0
//   0x10 NYET        if hird_sw > hird_hw, or data_pending
//   0x00 SUCCESS     otherwise
//
// USB_HUB_L1_RESPONSE_MODE selects it, and the matching +usb_hub_l1_expect
// plusarg tells the host sequence what to require. The two must agree; neither
// is independently meaningful.
//
// MCU firmware cannot read UVM plusargs and there is no mailbox between this
// image and the host sequence, so a run-time negotiation would have to be
// invented out of USB traffic - fragile, and circular (using the feature under
// test to configure the feature under test). A build-time switch is the same
// approach caliptra_ss_usb_hs_dev_lpm_l1.c takes for
// USB_LPM_DEVICE_INITIATED_EXIT.
//
//   USB_HUB_L1_RESPONSE_MODE = 0  default. LPM_SUP=1, HIRD_SW=0, NYET=0 on
//                                 BOTH controllers. Both ports answer 0x00 and
//                                 enter L1. Pair with +usb_hub_l1_expect=0.
//   USB_HUB_L1_RESPONSE_MODE = 1  HIRD_SW raised to 0xF on both, so any HIRD
//                                 the host sends is below it. Both ports must
//                                 answer 0x10 NYET and must NOT enter L1.
//                                 Pair with +usb_hub_l1_expect=1.
//   USB_HUB_L1_RESPONSE_MODE = 2  DEVCMDSTAT.LPM_SUP cleared on both. Both
//                                 ports must answer 0x30 and must NOT enter
//                                 L1. Pair with +usb_hub_l1_expect=2.
//
// The mode is applied to BOTH controllers so the two per-port legs of the host
// sequence see the same answer. Applying it to only one would make the test's
// expected value port-dependent for no benefit.
//
// NOTE ON MODE 1: NYET is forced via HIRD_SW rather than via LPM[8]
// DATA_PENDING deliberately. DATA_PENDING is also driven by hardware activity,
// so forcing it from firmware and then having real traffic clear it would make
// the refusal racy. HIRD_SW is a pure software field with no hardware writer,
// so the condition is stable for the whole run.
//
// NOTE ON HUB_CONTROL: this firmware never writes HUB_CONTROL directly. The
// hub's own LPM_SUP (HUB_CONTROL[11], reset 1) feeds the UPSTREAM PIE path
// (usbreg_lpm_sup) and is not what hub_l1_status consults for a downstream
// port, so clearing it would not produce a per-port refusal and would instead
// stop the hub advertising LPM at all.
//
// WHY POLLING AND NOT INTERRUPTS: the interrupt-driven dual-device idiom (see
// caliptra_ss_usb_dual_device_hs_bulk_loopback.c) needs USBDC1's IRQ looped
// back onto cptra_ss_mcu_ext_int[6], which costs a BUILD_CFLAGS define plus a
// matching +USB_HUB_COMPOUND_DEV1_IRQ plusarg. This test only has to service
// EP0 and watch two status registers, so it alternates usb_select_device()
// inside one polling loop instead and avoids that dependency entirely.
//
// NOTE ON SUSPEND CHECKING: the DUT-side suspend/resume checker is NOT armed by
// this test. There is a single shared UTMI SuspendM for the whole compound IP,
// so it cannot attribute a suspend to one port, and asserting on it here would
// be meaningless (or worse, would pass for the wrong reason). Per-port evidence
// comes from the two controllers' own DEVCMDSTAT.LPM_SUS bits, below, and from
// the host sequence's per-port PORT_L1 status checks.

#include "soc_address_map.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include "caliptra_ss_lib.h"
#include "usb.h"
#include "stdint.h"
#include "veer-csr.h"

// Runtime device retargeting for THIS translation unit.
//
// usb.h resolves the device-neutral USB_DEV_* macros against the COMPILE-TIME
// base chosen by USB_DEV_SEL. usb.c re-points them at usb_select_device()'s
// runtime choice, but that #undef/#define is scoped to usb.c. The code in this
// file reads USB_DEV_DEVCMDSTAT / USB_DEV_INTSTAT / USB_DEV_LPM directly, so
// without the same retargeting here every access would hit USBDC0 even while
// servicing USBDC1 - and the whole per-port isolation claim would be checked
// against one controller twice. Re-apply usb.c's exact trick.
#undef USB_DEV_CSR_BASE_ADDR
#undef USB_DEV_MEM_BASE_ADDR
#define USB_DEV_CSR_BASE_ADDR  usb_active_dev_csr_base()
#define USB_DEV_MEM_BASE_ADDR  usb_active_dev_mem_base()

// Poll loop ceiling. Sized to outlast hub enumeration, two device
// enumerations, and the two sequential per-port L1 enter/exit cycles the host
// sequence performs. Each iteration is only a few CSR reads.
#define USB_POLL_TIMEOUT 200000

// Number of embedded downstream device controllers. Port N+1 of the hub is
// wired to device N.
#define USB_NUM_DEVICES  2

// Selects which hub response the host will observe. See the header.
#ifndef USB_HUB_L1_RESPONSE_MODE
#define USB_HUB_L1_RESPONSE_MODE 0
#endif

// HIRD_SW value used by mode 1 to force a NYET. 0xF is the maximum, so it is
// greater than any HIRD the host can put in wIndex[7:4] except 0xF itself; the
// host sequence sends 0x1, so the comparison hird_sw > hird_hw holds.
#define USB_HUB_L1_NYET_HIRD_SW 0xFu

// In the refusal modes no port may enter L1, so the expected entry count per
// controller is 0 rather than 1.
#if (USB_HUB_L1_RESPONSE_MODE == 0)
#define USB_HUB_L1_EXPECT_ENTRIES 1u
#else
#define USB_HUB_L1_EXPECT_ENTRIES 0u
#endif

// Number of EP0 SETUPs each controller must answer, after the expected L1
// activity has been seen, before the MCU may halt.
//
// This is the end-of-test handshake, and it is deliberately counted in SETUPs
// rather than in poll iterations. A poll-iteration grace period does not work:
// iterations have no fixed relationship to host progress, so any constant is
// either too short (the MCU halts mid-transfer and the host sees a 0-byte
// GetDescriptor after a NAK timeout) or arbitrarily long. Counting SETUPs ties
// the halt directly to the host's own post-L1 traffic.
//
// The host sequence ends with exactly one GetDescriptor(Device) per device
// (post_l1_traffic_check at addresses 2 and 3), so one further SETUP on each
// controller means that final check has been served and nothing else is
// expected. See the "Operation" step 9 in the README - if that step ever grows
// another transfer per device, raise this to match.
#define USB_HUB_L1_TAIL_SETUPS 1u

// Hard ceiling on how many poll iterations to wait for those tail SETUPs, so a
// host that never sends them cannot hang the run. Reaching this is reported.
#define USB_HUB_L1_TAIL_POLL_MAX 60000u

volatile char* stdout = (char *)SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

// Per-controller L1 observation state. Index 0 = USBDC0 (hub port 1),
// index 1 = USBDC1 (hub port 2).
typedef struct {
    uint32_t lpm_events;      // DSUS_C events seen on this controller
    uint32_t l1_entry_count;  // transitions into LPM_SUS
    uint32_t l1_exit_count;   // transitions out of LPM_SUS
    uint32_t l1_active;       // last observed LPM_SUS level
    uint32_t l2_events;       // L2 suspends - should not happen, SOF stays on
    uint32_t hird_hw_last;    // HIRD_HW latched at the last entry
    uint32_t setup_count;     // EP0 SETUPs served, used for the tail handshake
} usb_dev_l1_state_t;

// Program the currently selected controller's LPM inputs so its hub port
// returns the response this build is meant to produce.
//
// Called after boot_usb_core_hub() for the device but BEFORE usb_hub_connect(),
// so the values are already in place when the host starts enumerating and could
// issue the request. Doing it after the connect would leave a window in which
// the hub would answer using the reset values instead.
static void usb_hub_l1_program_response_mode(int dev) {
    uint32_t devcmdstat;
    uint32_t lpm;

#if (USB_HUB_L1_RESPONSE_MODE == 1)
    // NYET leg: raise HIRD_SW above anything the host will send. HIRD_SW is
    // LPM[7:4]; HIRD_HW (LPM[3:0]) is read-only and tracks the received HIRD.
    lpm = lsu_read_32(USB_DEV_LPM);
    lpm &= ~DEV0_CSR_LPM_HIRD_SW_MASK;
    lpm |= (USB_HUB_L1_NYET_HIRD_SW << DEV0_CSR_LPM_HIRD_SW_LOW)
           & DEV0_CSR_LPM_HIRD_SW_MASK;
    lsu_write_32(USB_DEV_LPM, lpm);
    VPRINTF(LOW, "MCU: dev%d (port %d) mode 1 (NYET) - LPM=0x%x\n",
            dev, dev + 1, lsu_read_32(USB_DEV_LPM));

#elif (USB_HUB_L1_RESPONSE_MODE == 2)
    // STALL-code leg: clear this device's LPM_SUP, which is hub_lpm_sup(dev).
    //
    // This must be a raw lsu_write_32() rather than the library's
    // usb_devcmdstat_write() helper, and the reason is deliberate: that helper
    // unconditionally ORs LPM_SUP back in (see usb.c, "forces LPM_SUP so the
    // controller keeps advertising LPM support for the whole run"), so calling
    // it here would immediately undo the very thing this mode exists to do.
    // The helper is also static to usb.c and not exported, so it is not
    // reachable from here in any case.
    //
    // The usual hazard with a raw DEVCMDSTAT read-modify-write is the device
    // address: bits [6:0] read LIVE but write a STAGED copy, so writing back a
    // stale value would retarget the controller. That hazard does not apply
    // here because the value written back is the one just read live, i.e. the
    // address currently in force - staging the same value is a no-op. Do not
    // generalise this into other DEVCMDSTAT writes.
    //
    // boot_usb_core_hub() forces LPM_SUP on, so this must run after it.
    devcmdstat = lsu_read_32(USB_DEV_DEVCMDSTAT);
    lsu_write_32(USB_DEV_DEVCMDSTAT,
                 devcmdstat & ~DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK);
    devcmdstat = lsu_read_32(USB_DEV_DEVCMDSTAT);

    if (devcmdstat & DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK)
        VPRINTF(LOW, "MCU: ERROR dev%d mode 2 could not clear LPM_SUP (DEVCMDSTAT=0x%x); hub port %d will answer SUCCESS, not 0x30, and the test will misreport\n",
                dev, devcmdstat, dev + 1);
    else
        VPRINTF(LOW, "MCU: dev%d (port %d) mode 2 (STALL-code) - LPM_SUP cleared (DEVCMDSTAT=0x%x)\n",
                dev, dev + 1, devcmdstat);

#else
    // SUCCESS leg: nothing to program, but assert the preconditions rather
    // than assume them. A violation here means a later "port refused L1"
    // result is a firmware setup bug, not a design bug, and that is very hard
    // to tell apart from the host side.
    devcmdstat = lsu_read_32(USB_DEV_DEVCMDSTAT);
    lpm        = lsu_read_32(USB_DEV_LPM);

    if (!(devcmdstat & DEV0_CSR_DEVCMDSTAT_LPM_SUP_MASK))
        VPRINTF(LOW, "MCU: ERROR dev%d LPM_SUP clear (DEVCMDSTAT=0x%x); hub port %d will answer 0x30 instead of SUCCESS\n",
                dev, devcmdstat, dev + 1);
    if (lpm & DEV0_CSR_LPM_HIRD_SW_MASK)
        VPRINTF(LOW, "MCU: ERROR dev%d HIRD_SW non-zero (LPM=0x%x); hub port %d may answer NYET instead of SUCCESS\n",
                dev, lpm, dev + 1);
    if (lpm & DEV0_CSR_LPM_DATA_PENDING_MASK)
        VPRINTF(LOW, "MCU: ERROR dev%d DATA_PENDING set (LPM=0x%x); hub port %d will answer NYET instead of SUCCESS\n",
                dev, lpm, dev + 1);

    VPRINTF(LOW, "MCU: dev%d (hub port %d) ready for PORT_L1 - DEVCMDSTAT=0x%x LPM=0x%x\n",
            dev, dev + 1, devcmdstat, lpm);
#endif
}

// Service EP0 and classify suspend-change events for the currently selected
// controller. usb_select_device() must already have selected dev.
static void usb_service_device_l1(int dev, usb_dev_l1_state_t *st) {
    uint32_t devcmdstat;
    uint32_t intstat;
    uint32_t lpm_reg;

    // Hardware clears Active on all endpoints at bus reset, so EP0 must be
    // restored or the next SETUP is NAK'd and enumeration stalls.
    usb_handle_bus_reset();

    devcmdstat = lsu_read_32(USB_DEV_DEVCMDSTAT);
    intstat    = lsu_read_32(USB_DEV_INTSTAT);

    // EP0 service. The host enumerates the hub and BOTH devices before it
    // issues any PORT_L1 request, so this must keep running on both
    // controllers or the request is never sent.
    if (intstat & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
        lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0OUT_MASK);
        if (devcmdstat & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
            st->setup_count++;
            usb_handle_control_transfer();
        }
        else
            // Status-stage ZLP OUT of a control read completed; re-arm EP0 OUT
            // so the next SETUP is received.
            usb_ep0_arm_out();
    }
    if (intstat & DEV0_CSR_INTSTAT_EP0IN_MASK)
        lsu_write_32(USB_DEV_INTSTAT, DEV0_CSR_INTSTAT_EP0IN_MASK);

    if (!(devcmdstat & DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK))
        return;

    // DSUS_C is shared between the L2 and L1 state changes in this IP
    // (usb_reg_if.m.vhdl asserts it when either sync_suspend or
    // sync_lpm_suspend changes), so classify from the live state bits rather
    // than assuming which one moved.
    lpm_reg = lsu_read_32(USB_DEV_LPM);
    st->lpm_events++;

    if (devcmdstat & DEV0_CSR_DEVCMDSTAT_LPM_SUS_MASK) {
        st->l1_active = 1;
        st->l1_entry_count++;
        st->hird_hw_last = lpm_reg & DEV0_CSR_LPM_HIRD_HW_MASK;
        VPRINTF(LOW, "MCU: dev%d (port %d) L1 ENTRY #%d DEVCMDSTAT=0x%x LPM=0x%x HIRD_HW=%d\n",
                dev, dev + 1, st->l1_entry_count, devcmdstat, lpm_reg,
                (int)st->hird_hw_last);
    } else if (devcmdstat & DEV0_CSR_DEVCMDSTAT_DSUS_MASK) {
        // L2, not L1. SOF generation is left on for the whole of this test, so
        // an L2 means the link went idle unexpectedly and any L1 attribution
        // around it is suspect.
        st->l2_events++;
        VPRINTF(LOW, "MCU: dev%d L2 suspend event (not L1) DEVCMDSTAT=0x%x - SOF should not have stopped in this test\n",
                dev, devcmdstat);
    } else if (st->l1_active) {
        st->l1_active = 0;
        st->l1_exit_count++;
        VPRINTF(LOW, "MCU: dev%d (port %d) L1 EXIT #%d DEVCMDSTAT=0x%x LPM=0x%x\n",
                dev, dev + 1, st->l1_exit_count, devcmdstat, lpm_reg);
    } else {
        VPRINTF(LOW, "MCU: dev%d suspend-change event with no low-power state set DEVCMDSTAT=0x%x\n",
                dev, devcmdstat);
    }

    // DSUS_C is write-1-to-clear. Read-modify-write the LIVE value so no status
    // bit that changed in the meantime is clobbered.
    lsu_write_32(USB_DEV_DEVCMDSTAT,
        lsu_read_32(USB_DEV_DEVCMDSTAT) | DEV0_CSR_DEVCMDSTAT_DSUS_C_MASK);
}

void main(void) {
    uint32_t poll_count;
    int dev;
    usb_dev_l1_state_t dev_state[USB_NUM_DEVICES] = {0};

    // Poll index (1-based) at which both controllers first met the expected L1
    // activity. 0 means "not yet", which is why the latch below stores
    // poll_count + 1.
    uint32_t settle_start = 0u;

    // Per-controller SETUP counts latched at that moment. The tail handshake
    // below waits for each controller to serve USB_HUB_L1_TAIL_SETUPS more
    // SETUPs than it had then.
    uint32_t setup_at_settle[USB_NUM_DEVICES] = {0};

    VPRINTF(LOW, "=================\nMCU: USB dual-device HS hub per-port L1 test\n=================\n\n");

    boot_mcu();

    // Bring up BOTH controllers. boot_usb_core_hub() programs the hub (HUB_EN)
    // and the active device's EP list / DEVCMDSTAT / INTEN, and forces LPM_SUP
    // on. Program USBDC0 then USBDC1; the hub descriptor array is only frozen
    // once HUB_EN AND HUB_CONNECT are both set, so the second boot's HUB_EN
    // re-write is a harmless idempotent edge (HUB_CONNECT is still clear here).
    for (dev = 0; dev < USB_NUM_DEVICES; dev++) {
        usb_select_device(dev);
        boot_usb_core_hub();
    }

    // Steer the hub's PORT_L1 response on BOTH ports before the host can ask.
    // Runs after both boots (boot_usb_core_hub() forces LPM_SUP on, so mode 2
    // must undo it afterwards) and before the upstream connect.
    VPRINTF(LOW, "MCU: hub per-port L1 response mode %d\n",
            USB_HUB_L1_RESPONSE_MODE);
    for (dev = 0; dev < USB_NUM_DEVICES; dev++) {
        usb_select_device(dev);
        usb_hub_l1_program_response_mode(dev);
    }

    // Connect the hub upstream now that both controllers are fully programmed.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    // Release the unconditional UTMI clock request on both controllers so each
    // can actually drop its clock in L1. FORCE_NEEDCLK would otherwise hold
    // usbreg_pll_on -> clock_on and pin utmi_suspendm high.
    for (dev = 0; dev < USB_NUM_DEVICES; dev++) {
        usb_select_device(dev);
        usb_allow_clock_stop();
    }

    VPRINTF(LOW, "MCU: entering dual-device per-port L1 observation loop\n");

    // One loop, both controllers. The host drives port 1's L1 cycle and then
    // port 2's, so neither controller may be starved of EP0 service at any
    // point - alternating inside a single loop keeps both live without needing
    // USBDC1's interrupt routed to the PIC.
    //
    // Two-stage exit.
    //
    // Stage 1: wait until BOTH controllers have seen their expected number of
    // L1 entries and matching exits, and neither is still in L1.
    //
    // Stage 2: then serve USB_HUB_L1_TAIL_SETUPS further EP0 SETUPs on EACH
    // controller - the host's closing GetDescriptor to address 2 and address 3.
    // Only then halt.
    //
    // Stage 2 is essential and must be expressed in SETUPs, not in elapsed poll
    // iterations. Stage 1 completes while the host is still clearing port 2, so
    // halting there leaves the host's final two control transfers unanswered;
    // they then fail with "returned 0 payload bytes" after a NAK timeout, which
    // reads as a device fault rather than as a firmware that stopped early.
    //
    // Why the MCU must halt at all: caliptra_ss_usb_base_test only drops its
    // run_phase objection on the MCU halt, so running to the 200000-iteration
    // ceiling keeps the simulation open long after the sequence has finished -
    // indistinguishable from a hang.
    for (poll_count = 0; poll_count < USB_POLL_TIMEOUT; poll_count++) {
        uint32_t done = 1u;

        for (dev = 0; dev < USB_NUM_DEVICES; dev++) {
            usb_select_device(dev);
            usb_service_device_l1(dev, &dev_state[dev]);
        }

        if (settle_start == 0u) {
            // Stage 1.
            for (dev = 0; dev < USB_NUM_DEVICES; dev++) {
                if (dev_state[dev].l1_entry_count < USB_HUB_L1_EXPECT_ENTRIES ||
                    dev_state[dev].l1_exit_count  < USB_HUB_L1_EXPECT_ENTRIES ||
                    dev_state[dev].l1_active)
                    done = 0u;
            }

            // Latch once. Latching rather than re-arming matters: a spurious
            // later L1 entry must not be able to postpone the halt forever. It
            // is still counted and still reported by the verdict below.
            if (done) {
                settle_start = poll_count + 1u;
                for (dev = 0; dev < USB_NUM_DEVICES; dev++)
                    setup_at_settle[dev] = dev_state[dev].setup_count;
                VPRINTF(LOW, "MCU: expected L1 activity seen on both controllers at poll %d; now serving %d closing SETUP(s) per controller\n",
                        poll_count, USB_HUB_L1_TAIL_SETUPS);
            }
        } else {
            // Stage 2.
            uint32_t tail_done = 1u;

            for (dev = 0; dev < USB_NUM_DEVICES; dev++) {
                if ((dev_state[dev].setup_count - setup_at_settle[dev])
                        < USB_HUB_L1_TAIL_SETUPS)
                    tail_done = 0u;
            }

            if (tail_done) {
                VPRINTF(LOW, "MCU: closing SETUPs served on both controllers (dev0 %d, dev1 %d total) at poll %d; halting\n",
                        dev_state[0].setup_count, dev_state[1].setup_count,
                        poll_count);
                break;
            }

            if ((poll_count - settle_start) >= USB_HUB_L1_TAIL_POLL_MAX) {
                VPRINTF(LOW, "MCU: WARNING waited %d polls for the closing SETUPs and saw only dev0 %d, dev1 %d since the L1 activity completed; halting anyway. If the host reported a 0-byte GetDescriptor, raise USB_HUB_L1_TAIL_POLL_MAX or check whether the host sequence still ends with one control transfer per device\n",
                        USB_HUB_L1_TAIL_POLL_MAX,
                        dev_state[0].setup_count - setup_at_settle[0],
                        dev_state[1].setup_count - setup_at_settle[1]);
                break;
            }
        }

        if (poll_count % 50000 == 0 && poll_count > 0)
            VPRINTF(LOW, "MCU: [poll %d] dev0 ent=%d exi=%d act=%d stp=%d | dev1 ent=%d exi=%d act=%d stp=%d\n",
                    poll_count,
                    dev_state[0].l1_entry_count, dev_state[0].l1_exit_count,
                    dev_state[0].l1_active, dev_state[0].setup_count,
                    dev_state[1].l1_entry_count, dev_state[1].l1_exit_count,
                    dev_state[1].l1_active, dev_state[1].setup_count);
    }

    if (settle_start == 0u)
        VPRINTF(LOW, "MCU: WARNING poll ceiling reached without both controllers meeting the expected L1 activity; the verdict below says which one fell short\n");

    // Verdict. The host sequence owns the authoritative per-port PORT_L1 status
    // checks; these prints are the device-side corroboration and are the most
    // useful lines in the log when a host-side check fails, because they say
    // whether the hub level ever reached the right controller.
    //
    // The host drives one PORT_L1 request per port, so the expected per-
    // controller entry count is USB_HUB_L1_EXPECT_ENTRIES: 1 in the SUCCESS
    // build, 0 in a refusal build. In EITHER case a count of 2 would mean the
    // other port's request also suspended this controller - the per-port
    // isolation failure this test exists to catch.
    for (dev = 0; dev < USB_NUM_DEVICES; dev++) {
        usb_dev_l1_state_t *st = &dev_state[dev];

        if (st->l1_entry_count > USB_HUB_L1_EXPECT_ENTRIES + 1u)
            VPRINTF(LOW, "MCU: ERROR dev%d saw %d L1 entries, expected %d; a request addressed to the OTHER port appears to suspend this controller too (per-port isolation broken)\n",
                    dev, st->l1_entry_count, USB_HUB_L1_EXPECT_ENTRIES);
        else if (st->l1_entry_count != USB_HUB_L1_EXPECT_ENTRIES)
            VPRINTF(LOW, "MCU: ERROR dev%d saw %d L1 entries, expected %d in response mode %d\n",
                    dev, st->l1_entry_count, USB_HUB_L1_EXPECT_ENTRIES,
                    USB_HUB_L1_RESPONSE_MODE);
        else if (st->l1_exit_count != USB_HUB_L1_EXPECT_ENTRIES)
            VPRINTF(LOW, "MCU: ERROR dev%d saw %d L1 entries but %d exits; they must match (LPM_SUS stuck or spurious)\n",
                    dev, st->l1_entry_count, st->l1_exit_count);
#if (USB_HUB_L1_RESPONSE_MODE == 0)
        else
            VPRINTF(LOW, "MCU: dev%d per-port L1 cycle OK - 1 entry, 1 exit, HIRD_HW=%d, %d suspend-change events\n",
                    dev, (int)st->hird_hw_last, st->lpm_events);
#else
        else
            VPRINTF(LOW, "MCU: dev%d never entered L1, as required for a refused PORT_L1 request in response mode %d (%d suspend-change events)\n",
                    dev, USB_HUB_L1_RESPONSE_MODE, st->lpm_events);
#endif

        if (st->l1_active)
            VPRINTF(LOW, "MCU: ERROR dev%d still in L1 at end of test (LPM_SUS set)\n", dev);
        if (st->l2_events)
            VPRINTF(LOW, "MCU: ERROR dev%d saw %d L2 suspend events; SOF generation should never have stopped in this test\n",
                    dev, st->l2_events);
    }

    VPRINTF(LOW, "MCU: USB dual-device HS hub per-port L1 test complete\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
