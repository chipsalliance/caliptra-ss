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
// caliptra_ss_usb_dual_device_hs_dev0_hotplug - DEV0 hotplug isolation test.
//
// GOAL
//   Prove that USBDC0 (device0) connect/disconnect activity does NOT perturb
//   USBDC1 (device1) while USBDC1 is actively performing bulk loopback
//   operations.
//
//     USBDC1 : runs a REPEATING EP1 64-byte bulk OUT -> IN loopback for the
//              whole test. It must never see a bus reset, never lose its
//              assigned device address, and never need re-enumeration.
//     USBDC0 : is cycled through DEV0_TARGET_CYCLES disconnect / reconnect
//              iterations by toggling its DEVCMDSTAT.DCON bit, and is
//              re-enumerated by the host after each reconnect.
//
// Apertures and interrupts (same topology as the dual-device bulk loopback):
//   - USBDC0 (device0): CSR 0x2000_0000, MEM 0x3000_0000, PIC vector 3.
//   - USBDC1 (device1): CSR 0x2000_2000, MEM 0x3001_0000, PIC vector 6.
//
// USBDC0's IRQ is wired to cptra_ss_mcu_ext_int[3] in RTL. USBDC1's IRQ is NOT
// routed to the PIC in caliptra_ss_top.sv; instead the testbench loops the top
// level output cptra_ss_usb_dev1_irq_o back onto cptra_ss_mcu_ext_int[6], gated
// at runtime by $test$plusargs("USB_HUB_COMPOUND_DEV1_IRQ"). The matching
// define must ALSO be passed to this firmware's BUILD_CFLAGS so
// init_usb_interrupts() enables vector 6 and mcu_isr.h compiles in
// service_usb_dev1_intr(). Both are handled by this test's .yml.
//
// WHY TOGGLING DEV0 DCON IS A DOWNSTREAM-ONLY EVENT
//   From ip_xxx_3511_hs_mem_compound_structure.a.vhdl:
//     hub_port_connect(0) <= dev0_usbreg_dev_connect;  -- DEV0 DCON = port 1
//     hub_port_connect(1) <= dev1_usbreg_dev_connect;  -- DEV1 DCON = port 2
//     usb_dev_connect <= hub_connect when hub_enable_q = '1'
//                   else dev0_usbreg_dev_connect;
//     hub_connect     <= sync_VBusDebounced and hub_dcon_q;
//
//   Once HUB_EN is set, the UPSTREAM connect is driven by the hub's own
//   HUB_CONNECT bit, not by DEV0's DCON. So clearing DEV0 DCON drops hub
//   downstream port 1 only; the upstream link, the hub and USBDC1 on port 2
//   all stay up. This is why no VBUS cycling is needed here (contrast
//   caliptra_ss_usb_hs_dev_disconnect, which drives VBUS and tears down the
//   whole compound).
//
//   Port reset isolation follows from the same source:
//     dev0_portreset <= hub_port_reset(0) or sync_busreset
//     dev1_portreset <= hub_port_reset(1) or sync_busreset
//   DEV0's port-1 reset does not reach DEV1.
//
// SCENARIO
//   1. Bring up the hub once, then program BOTH USBDC0 and USBDC1 EP lists.
//   2. Enable PIC vectors 3 (dev0) and 6 (dev1) via init_usb_interrupts().
//   3. Connect the hub upstream. The host enumerates the hub, brings up
//      downstream ports 1 and 2 and enumerates USBDC0 (addr 2) and USBDC1
//      (addr 3).
//   4. USBDC1 loops: on each EP1 IN completion it re-arms EP1 OUT for the next
//      iteration and bumps dev1_loop_count.
//   5. Once USBDC1 is configured and has completed at least one loopback, the
//      DEV0 hotplug state machine starts cycling USBDC0:
//        HP_DISCONNECT        -> usb_set_device_connect(0) on dev0
//        HP_DISCONNECTED_HOLD -> stay detached long enough for the host to see
//                                hub port 1 go away (timer-ended)
//        HP_CONNECT           -> usb_set_device_connect(1) on dev0
//        HP_WAIT_REENUM       -> wait for the host to re-enumerate USBDC0
//                                (event-ended, not timed)
//      then repeat until DEV0_TARGET_CYCLES cycles are done.
//   6. The test PASSES when DEV0_TARGET_CYCLES hotplug cycles have completed,
//      USBDC1 has completed at least DEV1_TARGET_LOOPS loopbacks, and the
//      USBDC1 isolation invariants below never fired.
//
// USBDC1 ISOLATION INVARIANTS (the actual assertions of this test)
//   Once USBDC1 has been enumerated, for the remainder of the run:
//     - USBDC1 must never report DRES_C (a bus reset). DEV0's port reset must
//       not propagate to port 2.
//     - USBDC1's DEVCMDSTAT device address must never drop back to 0. A port
//       reset on port 2 would clear it.
//   Either event sets dev1_isolation_violation and fails the test.
//
// TERMINOLOGY - "HOLD" vs "WAIT"
//   The two non-action states of the hotplug FSM are deliberately named
//   differently, because they end for completely different reasons and
//   conflating them is what produced the earlier hangs:
//     - a HOLD is a state the firmware DELIBERATELY STAYS IN for a fixed amount
//       of time, because the device must remain in that electrical condition
//       long enough for the host to sample it. It is a minimum residency ended
//       by a clock deadline, and nothing external can shorten it.
//       HP_DISCONNECTED_HOLD is the only such state here: DEV0 must stay
//       detached for DEV0_DISCONNECT_HOLD_US so the host's 20 us hub port poll
//       cannot step over the disconnect edge and pass vacuously.
//     - a WAIT is a state the firmware stays in only until an external EVENT is
//       observed, with no intended duration at all. HP_WAIT_REENUM ends the
//       moment the host has finished re-enumerating USBDC0, which the firmware
//       confirms by seeing DEV0's bus address back at USBDC0_BUS_ADDR with EP1
//       re-armed; on a healthy run it is as short as the host makes it, and it
//       carries no timer of its own.
//   The earlier names (HP_OFF_DWELL / HP_ON_DWELL) suggested both were padding
//   delays bolted onto the sequence, which only HP_DISCONNECTED_HOLD is.
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
// CALIPTRA_SS_CLK_FREQ, used to convert the DEV0 disconnected hold from
// microseconds into MCU clock cycles.
#include "caliptra_ss_clk_freq.h"
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
// scoped to usb.c's translation unit only. The functions in THIS file access
// USB_DEV_* directly, so without the same retargeting here they would always
// hit USBDC0's aperture even while servicing USBDC1.
//
// Re-apply usb.c's exact trick: re-define the two base macros in terms of the
// runtime accessors usb_active_dev_csr_base() / usb_active_dev_mem_base()
// (exported from usb.c). Every derived macro in usb.h is expanded at its USE
// site, so re-pointing the bases makes all of them follow
// usb_select_device() in this file too.
#undef USB_DEV_CSR_BASE_ADDR
#undef USB_DEV_MEM_BASE_ADDR
#define USB_DEV_CSR_BASE_ADDR  usb_active_dev_csr_base()
#define USB_DEV_MEM_BASE_ADDR  usb_active_dev_mem_base()

// Overall firmware run budget: how long main() keeps polling before it gives up
// and halts.
//
// This is a SIMULATION-TIME control, not just a functional backstop. The UVM
// run_phase does NOT end when the host sequence finishes - the base test's
// phase_ready_to_end() raises an objection and holds it until the MCU asserts
// its halt status (csr_write_mpmc_halt() at the end of main()). The MCU, not the
// sequence, decides when the simulation ends.
//
// The previous ceiling was an iteration count (1500000 main-poll iterations),
// which was never a bounded amount of simulated time. Measured against this
// run: real activity ended at ~1.4 ms but VCS ran to 6.93 ms, i.e. 5.53 ms
// (80% of the run) was a dead tail of the MCU spinning on DCCM/CSR reads with
// nothing left to observe. At the observed iteration cost the 1500000-iteration
// ceiling would have taken 180-375 ms of simulated time to expire, so it was
// effectively infinite; the run only ended because the UVM objection timed out.
//
// Expressing the budget in TIME makes the worst-case tail bounded and
// predictable. The host sequence's own worst case is ~2.3 ms, so 3 ms lets the
// firmware always outlive the sequence and record its verdict, while capping
// the dead tail on a failing run at well under a millisecond.
#define USB_TEST_RUN_BUDGET_US        3000u

// Number of DEV0 disconnect/reconnect iterations. MUST match
// DEV0_HOTPLUG_CYCLES in
// caliptra_ss_usb_dual_device_hs_dev0_hotplug_sequence.svh.
#define DEV0_TARGET_CYCLES            3u

// USBDC1 loopback iterations required to pass: one per DEV0 cycle plus the
// baseline and the final one driven by the host sequence.
#define DEV1_TARGET_LOOPS             (DEV0_TARGET_CYCLES + 2u)

// Bus address the host assigns to USBDC0 on every enumeration. MUST match
// USBDC0_ADDR in caliptra_ss_usb_dual_device_hs_dev0_hotplug_sequence.svh.
//
// The firmware needs this value because it is the only evidence available to
// it that the host has actually re-enumerated USBDC0 after a reconnect: a hub
// port reset clears DEV_ADDR to 0, and only a host SET_ADDRESS can put this
// value back. See HP_WAIT_REENUM.
#define USBDC0_BUS_ADDR               2u

// DEV0 disconnected hold, expressed in TIME rather than in main-poll
// iterations.
//
// The hold has to sit inside a window with both a floor and a ceiling:
//
//   floor   - it must outlast the host sequence's hub port-1 poll interval
//             (PORT_POLL_INTERVAL = 20 us) so the host cannot miss the
//             disconnect edge entirely and pass vacuously.
//   ceiling - it must expire well before the host's RECONNECT poll budget is
//             exhausted. That budget is PORT_POLL_MAX_ATTEMPTS (60) polls of
//             (20 us interval + ~2.6 us GetPortStatus transfer) ~= 1356 us,
//             measured from the moment the host observed the disconnect.
//
// A raw loop count cannot honour that ceiling, because one main-poll iteration
// is not a stable unit of time: its cost depends on how many register reads and
// VPRINTFs that particular iteration performs. The previous value of 40000
// iterations was an unanchored guess and was far over the ceiling - DEV0 DCON
// fell at ~766 us and the hold had still not expired when the host sequence
// finished at ~2269 us, so HP_CONNECT was never reached and DCON never went
// back high at all. In the waves DEV0_USBREG_DEV_CONNECT simply drops once and
// stays low; "DCON set (port 1 up)" never prints. That is the
// "Hub port 1 never reached CONNECT_STATUS=1 within 60 polls" failure: not a
// missed edge, but a reconnect that the firmware never performed.
//
// The floor is also higher than just one poll interval, because the host does
// real WORK inside the detached window before it starts polling for the
// reconnect. Measured from the failing run: it observed the disconnect at
// 779633 ns, cleared the port connection change, waited POST_BULK_OUT_SETTLE
// (20 us), ran the USBDC1 BULK IN and checked the loopback payload, finishing
// at 809632 ns - about 30 us. Only then did it begin waiting for port 1 to
// come back. If DCON were re-asserted before that, the host could step
// straight from "down" to "up" and the reconnect would not be a clean edge.
//
// 300 us is ~15 host poll intervals and ~10x the host's in-window work, so
// the disconnect is unambiguously observable from both directions, while still
// leaving ~1050 us of the ~1356 us reconnect budget for re-enumeration. The
// previous 200 us also satisfied both bounds; it is raised here only to widen
// the margin now that the window's contents are known, and because the
// re-enumeration handshake in HP_WAIT_REENUM means a longer hold no longer
// risks the firmware running ahead of the host.
#define DEV0_DISCONNECT_HOLD_US     300u

// CALIPTRA_SS_CLK_FREQ is in MHz (boot_i3c_socmgmt_if() prints it as "%u MHz"),
// so it is exactly the number of MCU clock cycles per microsecond.
#define MCU_CYCLES_PER_US             ((uint64_t)CALIPTRA_SS_CLK_FREQ)
#define DEV0_DISCONNECT_HOLD_CYCLES \
    ((uint64_t)DEV0_DISCONNECT_HOLD_US * MCU_CYCLES_PER_US)
#define USB_TEST_RUN_BUDGET_CYCLES \
    ((uint64_t)USB_TEST_RUN_BUDGET_US * MCU_CYCLES_PER_US)

// EP1 OUT / IN data buffers in each controller's packet SRAM. EP0 uses
// 0x000-0x1FF, so EP1 buffers are placed after it. Both controllers use the
// same offsets inside their own MEM aperture.
#define USB_SRAM_EP1_OUT_BUF_OFFSET   0x200u
#define USB_SRAM_EP1_IN_BUF_OFFSET    0x240u

// EP command/status list byte offsets (NXP IP_3511 Integration Guide s4.2.3).
#define USB_EP_LIST_EP0_OUT_OFFSET    0x000u
#define USB_EP_LIST_EP1_OUT_OFFSET    0x010u
#define USB_EP_LIST_EP1_IN_OFFSET     0x018u

// 64-byte bulk loopback (HS EP1 bulk). Matches the host sequence's
// LOOPBACK_BYTES.
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

// DEV0 hotplug state machine states.
typedef enum {
    HP_WAIT_DEV1_UP = 0,  // event: until USBDC1 is enumerated and looping
    HP_DISCONNECT,        // clear DEV0 DCON
    HP_DISCONNECTED_HOLD, // timed: stay detached long enough to be observed
    HP_CONNECT,           // re-assert DEV0 DCON
    HP_WAIT_REENUM,       // event: until the host re-enumerates USBDC0
    HP_DONE               // all cycles complete
} dev0_hotplug_state_t;

// Per-device loopback progress. Index 0 = USBDC0, 1 = USBDC1.
typedef struct {
    bool     ep1_armed;      // EP1 OUT armed and EP1OUT interrupt enabled
    bool     loopback_armed; // EP1 OUT data copied to EP1 IN and EP1 IN armed
    bool     enumerated;     // has been seen configured at least once
    uint32_t loop_count;     // completed EP1 OUT -> IN loopbacks
} usb_dev_loopback_state_t;

static dev0_hotplug_state_t dev0_hp_state   = HP_WAIT_DEV1_UP;
static uint32_t             dev0_cycle_count = 0u;

// mcycle value at which the current HP_DISCONNECTED_HOLD expires. Captured when
// DCON is cleared, so the hold is a real elapsed-time deadline rather than a
// count of variable-cost poll iterations.
static uint64_t             dev0_disconnect_hold_deadline = 0u;

// Set if USBDC1 was ever disturbed while DEV0 was being hotplugged. This is the
// headline failure condition of the test.
static bool dev1_isolation_violation = false;

// Read back an EP command/status entry until its Active bit is observed SET,
// so the caller knows the arm has landed in the EP list before any completion
// polling is done against it.
//
// The EP-list lives in the controller's packet SRAM and the arming store is
// posted, so an immediately following load can still return the pre-arm value.
// Bounding the spin keeps a genuinely unresponsive controller from hanging the
// whole test; the entry is polled only a handful of times in practice.
#define USB_EP_ARM_CONFIRM_LIMIT 1000u
static void usb_ep1_confirm_armed(uint32_t ep_list_offset, const char *what) {
    uint32_t spins;

    for (spins = 0; spins < USB_EP_ARM_CONFIRM_LIMIT; spins++) {
        if (lsu_read_32(USB_DEV_DMA_BASE_ADDR + ep_list_offset)
            & USB_EP_ENTRY_ACTIVE)
            return;
    }

    VPRINTF(LOW, "MCU: WARNING - dev%d %s Active never read back set after "
            "arming (%d reads)\n",
            usb_get_active_device(), what, USB_EP_ARM_CONFIRM_LIMIT);
}

// Arm EP1 OUT for the currently selected device and enable its EP1OUT
// interrupt so the EP1 OUT completion is published to the ISR mailbox.
// usb_select_device() must already have selected the target device, so the
// USB_DEV_* aliases resolve to that controller's aperture.
// USB_EP_ENTRY_TOGGLE_RESET (bit 28) is set on every re-arm. Unlike the
// single-shot dual-device bulk loopback reference, this test runs EP1 OUT and
// EP1 IN many times on the SAME endpoint, so the device's data toggle would
// keep alternating DATA0/DATA1 across iterations. The host side does not track
// that: every dev1_loopback() retargets the VIP with host_agent_h.reconfigure()
// and so restarts from a DATA0 expectation, which showed up as
//   data_toggle_check_Dev3_EP1_IN: Received Data packet with incorrect PID
//   name : DATA1. Expecting DATA0 for DATA stage
// Arming with TR=1 forces the endpoint back to DATA0 for the next packet
// (usb_ep_config_handler.m.vhdl: reg_ep_toggle_reset <= upd_dma_wdata(28)), so
// each iteration starts from the same toggle state the host expects.
static void usb_ep1_out_arm(void) {
    uint32_t ep1_out = USB_EP_ENTRY_ACTIVE
                     | USB_EP_ENTRY_TOGGLE_RESET
                     | USB_EP_ENTRY_NBYTES(USB_BULK_LOOPBACK_BYTES)
                     | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                             + USB_SRAM_EP1_OUT_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET, ep1_out);

    // Confirm the arm is visible to the MCU before returning. The EP-list write
    // above is posted, so a read performed later in the SAME poll iteration can
    // still observe Active == 0. The service loop used to cope with that by
    // requiring Active to be observed SET before accepting a clear as a
    // completion, but that is a livelock: hardware only ever CLEARS Active, it
    // never sets it, so if the very first read misses the set state the
    // "observed set" condition can never be satisfied afterwards and the
    // endpoint is never recognised as complete. That is exactly what stalled
    // USBDC1 in hotplug cycle 0 - EP1 OUT was armed at 771610 ns, the host's
    // OUT completed at 782266 ns, and "dev1 EP1 IN armed (loopback)" never
    // appeared, so the following BULK IN hit an un-armed endpoint and returned
    // an empty payload. Confirming the set state here, at arm time, removes the
    // two-phase observation and the livelock with it.
    usb_ep1_confirm_armed(USB_EP_LIST_EP1_OUT_OFFSET, "EP1 OUT");

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

    // TR=1 for the same reason as in usb_ep1_out_arm(): this is a repeated
    // re-arm of EP1 IN and the host restarts from a DATA0 expectation after
    // every VIP address retarget.
    ep1_in = USB_EP_ENTRY_ACTIVE
           | USB_EP_ENTRY_TOGGLE_RESET
           | USB_EP_ENTRY_NBYTES(USB_BULK_LOOPBACK_BYTES)
           | USB_EP_ENTRY_ABS_ADDR(USB_DEV_DMA_BASE_ADDR
                                   + USB_SRAM_EP1_IN_BUF_OFFSET);
    lsu_write_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_IN_OFFSET, ep1_in);

    // Same posted-write confirmation as in usb_ep1_out_arm().
    usb_ep1_confirm_armed(USB_EP_LIST_EP1_IN_OFFSET, "EP1 IN");

    VPRINTF(LOW, "MCU: dev%d EP1 IN armed (loopback)\n", usb_get_active_device());
}

// Returns true once the selected device's EP1 IN transfer has completed, i.e.
// hardware cleared the Active bit on the EP1 IN command/status entry.
static bool usb_ep1_in_complete(void) {
    return (lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_IN_OFFSET)
            & USB_EP_ENTRY_ACTIVE) == 0u;
}

// Returns true once the selected device's EP1 OUT transfer has completed, i.e.
// hardware cleared the Active bit on the EP1 OUT command/status entry and the
// received bytes are therefore present in the EP1 OUT buffer.
static bool usb_ep1_out_complete(void) {
    return (lsu_read_32(USB_DEV_DMA_BASE_ADDR + USB_EP_LIST_EP1_OUT_OFFSET)
            & USB_EP_ENTRY_ACTIVE) == 0u;
}

// NOTE for anyone tempted to add private EP0 entry manipulation back here:
// this is where USB_EP0_OUT_NBYTES_FIELD / USB_EP0_OUT_SETUP_NBYTES and the
// usb_ep0_out_unarmed() / usb_ep0_arm_out_sized() / usb_ep0_repair_out_nbytes()
// helpers used to live. They were removed in the round-12 convergence. EP0 is
// now owned entirely by the shared library (usb_handle_control_transfer() and
// usb_ep0_arm_out()), exactly as in the passing hs_bulk_loopback reference.
// One fact worth keeping from that experiment: an un-armed EP0 OUT is NOT
// equivalent to DEVCMDSTAT.SETUP. A SETUP lands in the controller's dedicated
// SETUP buffer descriptor and does not consume the EP0 OUT arm, so testing the
// entry's Active bit as a "control packet is waiting" gate deadlocks
// enumeration on both controllers. Only DEVCMDSTAT.SETUP reports a pending
// SETUP.

// Returns the device address currently latched in the selected controller's
// DEVCMDSTAT. Used by the USBDC1 isolation invariant: a port reset on port 2
// would clear this back to 0.
static uint32_t usb_get_device_address(void) {
    return (lsu_read_32(USB_DEV_DEVCMDSTAT)
            & DEV0_CSR_DEVCMDSTAT_DEV_ADDR_MASK)
           >> DEV0_CSR_DEVCMDSTAT_DEV_ADDR_LOW;
}

// Returns true when the selected controller is currently attached, i.e. its
// DCON bit is set. Clearing DCON detaches the device from its hub port but
// does NOT clear DEV_ADDR or the configured state, so "configured" alone is
// not sufficient evidence that the device is on the bus.
static bool usb_is_connected(void) {
    return (lsu_read_32(USB_DEV_DEVCMDSTAT)
            & DEV0_CSR_DEVCMDSTAT_DCON_MASK) != 0u;
}

// USBDC0's device address, selecting USBDC0 explicitly first.
//
// This exists because usb_get_device_address() reads whichever controller
// usb_select_device() last pointed at, and the hotplug FSM runs from main()
// AFTER usb_service_device(1, ...), so the active selection on entry is
// USBDC1, not USBDC0. HP_WAIT_REENUM would otherwise be comparing USBDC1's
// address (3) against USBDC0's expected address (2) and could never be
// satisfied. Any new hotplug-FSM state that reads a DEV0 register must either
// use a helper like this one or call usb_select_device(0) itself.
static uint32_t usb_get_dev0_address(void) {
    usb_select_device(0);
    return usb_get_device_address();
}

// Drain the ISR mailbox and advance the loopback state machine for one device.
// dev selects USBDC0 (0) or USBDC1 (1); usb_events is the snapshot of the
// matching mailbox field. The ISR has already W1C-acknowledged INTSTAT, so the
// foreground must not touch INTSTAT itself. EP1 IN completion is detected by
// polling the EP list Active bit (not INTSTAT), matching the polling loopback
// reference.
//
// For dev==1 this also enforces the isolation invariants: once USBDC1 has been
// enumerated it must never see a bus reset and must never lose its address.
static void usb_service_device(int dev, uint32_t usb_events,
                               usb_dev_loopback_state_t *st) {
    usb_select_device(dev);

    // Bus reset handling. DRES_C must be SAMPLED ONCE, BEFORE anything is
    // allowed to clear it, and every consequence of the reset driven off that
    // single sample.
    //
    // This used to be two steps: an unconditional usb_handle_bus_reset(),
    // followed by an "if (usb_events & DEV_INT)" block that re-read DEVCMDSTAT
    // and acted on DRES_C. That is broken, because usb_handle_bus_reset() is
    // self-guarded on DRES_C and W1C-CLEARS it as part of handling
    // (usb.c: usb_devcmdstat_write(cmd | DRES_C) before usb_ep0_reinit()). The
    // first call therefore CONSUMED the bit and the second block could never
    // see it. Two things silently never happened:
    //
    //   1. ep1_armed / loopback_armed were never cleared, so a reset arriving
    //      while EP1 was armed left stale loopback state behind. Hardware had
    //      already cleared Active on every endpoint, but the firmware still
    //      believed EP1 was armed, so it neither re-armed EP1 OUT nor restarted
    //      the loopback - it waited forever on an endpoint the controller had
    //      disarmed underneath it.
    //   2. MUCH WORSE for this test: the dev1 ISOLATION VIOLATION check sat in
    //      that same dead block. The headline assertion - "USBDC1 must never
    //      see a bus reset while DEV0 is hotplugged" - could therefore NEVER
    //      FIRE, and a real isolation failure would have been reported as a
    //      PASS. A test that cannot fail is worse than no test at all.
    //
    // Sampling first and handling second makes both consequences unconditional
    // and keeps the invariant observable. The sample must also be taken before
    // the EP0 SETUP servicing below, which calls into the same library.
    //
    // This is deliberately NOT gated on usb_events & DEV_INT_MASK, for the same
    // reason the EP0 SETUP check below is not gated on EP0OUT: DRES_C is a
    // sticky hardware status bit, whereas the mailbox event is a one-shot that
    // two equal-priority controllers can lose. Gating a sticky bit behind a
    // losable event just reintroduces the round-8 class of bug.
    //
    // The EP1 state is cleared UNCONDITIONALLY rather than under
    // "if (st->ep1_armed)". A bus reset invalidates the arm state whether or not
    // the firmware currently thinks EP1 is armed, so there is no case in which
    // keeping it is correct.
    {
        uint32_t cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

        if (cmd & DEV0_CSR_DEVCMDSTAT_DRES_C_MASK) {
            // ISOLATION INVARIANT: USBDC1 must not see a bus reset once it has
            // been enumerated. DEV0's hub port-1 reset must not reach port 2.
            if (dev == 1 && st->enumerated) {
                dev1_isolation_violation = true;
                VPRINTF(LOW, "MCU: ISOLATION VIOLATION - dev1 saw a bus reset "
                        "(DRES_C) during DEV0 hotplug activity\n");
            }

            // Restores the EP0 entries and W1C-clears DRES_C.
            usb_handle_bus_reset();

            st->ep1_armed      = false;
            st->loopback_armed = false;
            VPRINTF(LOW, "MCU: dev%d bus reset - EP1 state cleared\n", dev);
        }
    }

    // EP0 control-transfer servicing, rebuilt VERBATIM from the passing
    // caliptra_ss_usb_dual_device_hs_bulk_loopback reference.
    //
    // History, so this is not re-complicated a fifth time: rounds 8-11 grew
    // five private EP0 helpers here (usb_ep0_setup_pending,
    // usb_service_ep0, usb_ep0_out_unarmed, usb_ep0_repair_out_nbytes,
    // usb_ep0_arm_out_sized) plus an EP0-only pass over both controllers at
    // the top of main(). Each was added to compensate for a symptom created
    // by the previous one, and every round's fix became the next round's
    // bug. They are all gone. The reference enumerates BOTH controllers and
    // loops back on both with exactly the two branches below, which proves
    // the library path (usb_handle_control_transfer / usb_ep0_arm_out) is
    // sound for two devices. The hotplug test's remaining differences are
    // the hotplug FSM, the isolation invariants and the loop counting -
    // nothing about EP0 needs to differ.
    //
    // Note the gate: EP0 is touched ONLY when the ISR actually reported an
    // EP0 OUT event. Polling DEVCMDSTAT unconditionally every iteration, as
    // the stripped usb_service_ep0() did, costs two extra register reads per
    // controller per iteration for no benefit - the SETUP bit is sticky and
    // the ISR always raises EP0OUT alongside it.
    if (usb_events & DEV0_CSR_INTSTAT_EP0OUT_MASK) {
        uint32_t ep0_cmd = lsu_read_32(USB_DEV_DEVCMDSTAT);

        if (ep0_cmd & DEV0_CSR_DEVCMDSTAT_SETUP_MASK) {
            // SETUP packet - decode and respond. This re-arms EP0.
            usb_handle_control_transfer();
        } else {
            // Status-stage ZLP OUT for a control read completed. Re-arm EP0
            // OUT so the next SETUP is received instead of NAK'd.
            usb_ep0_arm_out();
        }
    }

    // EP0 IN completion needs no action: the ISR already acknowledged it.

    // Arm EP1 OUT once the device is configured (enumeration complete) AND
    // still attached. This is idempotent and only (re-)arms when not already
    // armed.
    //
    // The usb_is_connected() term is essential for this test and was the bug
    // behind the "host and firmware ran different hotplug cycles" failure.
    // Clearing DEV0 DCON detaches the device from hub port 1, but it does NOT
    // clear DEV_ADDR or the SET_CONFIGURATION state, so usb_is_configured()
    // stays TRUE across the whole detached window. HP_DISCONNECT therefore
    // cleared ep1_armed, and this branch re-armed it ~2 us later while the
    // device was physically off the bus. That stale arm then satisfied
    // HP_WAIT_REENUM immediately after DCON was re-asserted, so the firmware
    // declared the cycle "re-enumerated" before the host had sent a single
    // packet, re-cleared DCON, and every host _dev0_recon SETUP correctly
    // ABORTED into a detached device.
    //
    // Gating on DCON means EP1 can only be re-armed once the device is back on
    // the bus, and - because a reconnect always brings a host port reset which
    // clears the configured state - only after the host has genuinely
    // re-enumerated it.
    if (!st->ep1_armed && usb_is_connected() && usb_is_configured()) {
        usb_ep1_out_arm();
        st->ep1_armed      = true;
        st->loopback_armed = false;
        if (!st->enumerated) {
            st->enumerated = true;
            VPRINTF(LOW, "MCU: dev%d enumerated (addr=%d)\n",
                    dev, usb_get_device_address());
        }
    }

    // ISOLATION INVARIANT: once enumerated, USBDC1 must keep its assigned bus
    // address. A port reset on hub port 2 would clear DEV_ADDR back to 0.
    if (dev == 1 && st->enumerated && usb_get_device_address() == 0u) {
        dev1_isolation_violation = true;
        VPRINTF(LOW, "MCU: ISOLATION VIOLATION - dev1 lost its device address "
                "(DEV_ADDR=0) during DEV0 hotplug activity\n");
    }

    // EP1 OUT completion: copy the received bytes to the EP1 IN buffer and arm
    // EP1 IN for the loopback.
    //
    // This is driven off the EP1 OUT entry's Active bit (hardware truth), NOT
    // off the mailbox EP1OUT event bit. The dual-device bulk loopback reference
    // can use the event bit because it performs exactly ONE loopback per
    // controller and latches it with a sticky "done" flag, so a spurious or
    // stale event can only ever fire once, before any data matters. This test
    // re-arms EP1 OUT repeatedly for USBDC1, which re-opens that window on
    // every iteration: usb_ep1_out_arm() sets INTEN.EP1OUT without first
    // clearing a pending INTSTAT.EP1OUT, so a left-over event bit makes the
    // copy run while the EP1 OUT buffer is still empty. EP1 IN is then armed
    // with zeros and loopback_armed is already set, so the block is skipped
    // when the real OUT data finally lands - and the host's BULK IN reads back
    // 64 zero bytes. Polling the Active bit instead guarantees the data is in
    // the buffer before it is copied.
    //
    // The arm itself is confirmed inside usb_ep1_out_arm() via
    // usb_ep1_confirm_armed(), so a cleared Active bit here is unambiguously a
    // completion and this test can be a single-phase check. It must NOT be
    // turned back into an "observe set, then observe clear" gate: hardware only
    // ever clears Active, so a single missed read of the set state would make
    // the set condition permanently unsatisfiable and stall the endpoint
    // forever.
    if (st->ep1_armed && !st->loopback_armed && usb_ep1_out_complete()) {
        usb_ep1_loopback_arm_in();
        st->loopback_armed = true;
    }

    // EP1 IN completion: this loopback iteration is done. USBDC1 immediately
    // re-arms EP1 OUT for the next iteration so it keeps operating across the
    // whole DEV0 hotplug sequence; USBDC0 is re-armed by the enumeration branch
    // above after each reconnect.
    //
    // Single-phase, for the same reason as the EP1 OUT check above: the arm was
    // already confirmed visible by usb_ep1_confirm_armed() inside
    // usb_ep1_loopback_arm_in(), so a cleared Active bit cannot be a stale
    // pre-arm read.
    if (st->loopback_armed && usb_ep1_in_complete()) {
        st->loop_count++;
        st->loopback_armed = false;
        VPRINTF(LOW, "MCU: dev%d EP1 bulk loopback #%d complete\n",
                dev, st->loop_count);

        if (dev == 1) {
            // Re-arm for the next USBDC1 iteration.
            usb_ep1_out_arm();
        } else {
            // USBDC0 is about to be disconnected again; let the enumeration
            // branch re-arm it after the next reconnect.
            st->ep1_armed = false;
        }
    }
}

// Advance the DEV0 hotplug state machine. Called once per main poll iteration.
// dev1_st is used only to gate the start of cycling on USBDC1 being up and
// already looping, so the disconnects genuinely overlap USBDC1 traffic.
static void dev0_hotplug_step(usb_dev_loopback_state_t *dev0_st,
                              const usb_dev_loopback_state_t *dev1_st) {
    switch (dev0_hp_state) {
    case HP_WAIT_DEV1_UP:
        // Only start perturbing DEV0 once USBDC1 is enumerated and has proven
        // it can complete a loopback. Otherwise a USBDC1 failure could not be
        // attributed to the hotplug activity.
        if (dev1_st->enumerated && dev1_st->loop_count > 0u) {
            VPRINTF(LOW, "MCU: dev1 up and looping - starting DEV0 hotplug "
                    "cycles (%d requested)\n", DEV0_TARGET_CYCLES);
            dev0_hp_state = HP_DISCONNECT;
        }
        break;

    case HP_DISCONNECT:
        // Clearing DEV0 DCON drops hub downstream port 1 only. The upstream
        // link is held up by the hub's own HUB_CONNECT bit, so USBDC1 on port 2
        // is unaffected.
        usb_select_device(0);
        usb_set_device_connect(0u);
        dev0_st->ep1_armed      = false;
        dev0_st->loopback_armed = false;
        VPRINTF(LOW, "MCU: DEV0 hotplug cycle %d - DCON cleared (port 1 down, "
                "reconnecting in %d us)\n",
                dev0_cycle_count + 1u, DEV0_DISCONNECT_HOLD_US);
        dev0_disconnect_hold_deadline = csr_read_mcycle()
                             + DEV0_DISCONNECT_HOLD_CYCLES;
        dev0_hp_state = HP_DISCONNECTED_HOLD;
        break;

    case HP_DISCONNECTED_HOLD:
        // Stay disconnected long enough for the host to poll hub port 1 and
        // observe CURRENT_CONNECT_STATUS == 0, then reconnect well inside the
        // host's reconnect poll budget. Timed off mcycle so the hold is the
        // intended number of microseconds regardless of how expensive each
        // main-poll iteration happens to be.
        if (csr_read_mcycle() >= dev0_disconnect_hold_deadline)
            dev0_hp_state = HP_CONNECT;
        break;

    case HP_CONNECT:
        // usb_set_device_connect(1) waits for VBUS_DEBOUNCED before setting
        // DCON, matching the library's connect sequencing.
        usb_select_device(0);
        usb_set_device_connect(1u);
        VPRINTF(LOW, "MCU: DEV0 hotplug cycle %d - DCON set (port 1 up)\n",
                dev0_cycle_count + 1u);
        dev0_hp_state = HP_WAIT_REENUM;
        break;

    case HP_WAIT_REENUM:
        // The cycle is complete once the host has re-enumerated USBDC0.
        //
        // Both terms below are required, and the address term is the one that
        // makes this a real handshake with the host rather than a self-check:
        //
        //   usb_get_dev0_address() == USBDC0_BUS_ADDR
        //       DEV_ADDR can only become non-zero because the host completed a
        //       SET_ADDRESS on this controller. A reconnect brings a hub port
        //       reset first, which clears DEV_ADDR to 0, so observing the
        //       expected address again is positive proof that THIS cycle's
        //       re-enumeration actually ran on the wire.
        //   dev0_st->ep1_armed
        //       SET_CONFIGURATION has also completed, so the device is fully
        //       usable again and not merely addressed.
        //
        // This state used to test ep1_armed ALONE, and that was the bug behind
        // the "host and firmware ran different hotplug cycles" failure. EP1 was
        // being re-armed by usb_service_device() while DEV0 was still detached
        // (DCON cleared does not clear the configured state - see the
        // usb_is_connected() note there), so this condition was already true
        // the instant DCON went back high. The firmware counted the cycle about
        // 3 us after HP_CONNECT with ZERO host traffic in between, immediately
        // re-cleared DCON for the next cycle, and the host's subsequent
        // re-enumeration SETUPs hit a detached device and aborted. The
        // usb_is_connected() gate fixes the stale re-arm; requiring the address
        // as well makes the handshake robust even if some future change
        // re-opens that window.
        //
        // There is no timeout here on purpose: the host sequence already fails
        // loudly if port 1 never comes back, and the main loop has its own
        // USB_TEST_RUN_BUDGET_US backstop.
        if (dev0_st->ep1_armed
            && usb_get_dev0_address() == USBDC0_BUS_ADDR) {
            dev0_cycle_count++;
            VPRINTF(LOW, "MCU: DEV0 hotplug cycle %d complete "
                    "(re-enumerated, dev1 loops so far=%d)\n",
                    dev0_cycle_count, dev1_st->loop_count);
            dev0_hp_state = (dev0_cycle_count >= DEV0_TARGET_CYCLES)
                          ? HP_DONE : HP_DISCONNECT;
        }
        break;

    case HP_DONE:
    default:
        break;
    }
}

void main(void) {
    uint32_t poll_count;
    usb_dev_loopback_state_t dev_state[2] = {0};
    bool passed = false;
    uint64_t run_deadline;

    VPRINTF(LOW, "=================\nMCU: USB dual-device HS DEV0 hotplug "
            "isolation test\n=================\n\n");

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
    // HUB_CONNECT stays set for the whole test: it is what keeps the upstream
    // link alive while DEV0's DCON is toggled underneath it.
    usb_hub_connect();

    mcu_cptra_advance_brkpoint();
    mcu_cptra_user_init();
    mcu_cptra_poll_mb_ready();

    VPRINTF(LOW, "MCU: Caliptra ready, entering DEV0 hotplug event loop\n");

    // The overall run budget is anchored to mcycle, so the worst-case dead
    // tail on a failing run is a real elapsed-time bound rather than a count
    // of variable-cost poll iterations. poll_count is only a diagnostic (how
    // much polling was needed) plus the gate for the rare progress dump below;
    // it is never a termination condition.
    //
    // The progress dump is deliberately NOT anchored to mcycle - see the long
    // note at its call site for why a wall-clock dump cadence broke
    // enumeration.
    run_deadline = csr_read_mcycle() + USB_TEST_RUN_BUDGET_CYCLES;

    for (poll_count = 0; csr_read_mcycle() < run_deadline; poll_count++) {
        uint32_t ev0;
        uint32_t ev1;

        // Snapshot then clear by complement so bits the ISR sets while we are
        // handling this batch are not lost.
        ev0 = mcu_intr_rcv.usb;
        mcu_intr_rcv.usb &= ~ev0;
        ev1 = mcu_intr_rcv.usb_dev1;
        mcu_intr_rcv.usb_dev1 &= ~ev1;

        // Service USBDC0 (vector 3) and USBDC1 (vector 6).
        usb_service_device(0, ev0, &dev_state[0]);
        usb_service_device(1, ev1, &dev_state[1]);

        // Drive the DEV0 connect/disconnect cycling.
        dev0_hotplug_step(&dev_state[0], &dev_state[1]);

        // Abort early on an isolation violation: the headline property of the
        // test has already been broken, so there is nothing left to prove.
        if (dev1_isolation_violation)
            break;

        if (dev0_cycle_count >= DEV0_TARGET_CYCLES
            && dev_state[1].loop_count >= DEV1_TARGET_LOOPS) {
            passed = true;
            break;
        }

        // Periodic progress dump, COUNT-gated like the reference rather than
        // wall-clock gated.
        //
        // This replaces an "every 100 us of mcycle" dump that was the direct
        // cause of the round-11 regression. VPRINTF serialises ONE CHARACTER
        // AT A TIME into MCI DEBUG_OUT (~28.6 ns/char at 400 MHz), so the old
        // ~184-character dump blocked the single-threaded service loop for
        // ~5.3 us. The host spaces enumeration SETUPs ~5 us apart, so a
        // 100 us cadence was guaranteed to land inside an enumeration burst
        // sooner or later, and the "no SETUP pending right now" guard it was
        // given could not help: a point-in-time gate cannot protect a
        // critical section LONGER than the gap it is waiting for. The proof
        // is in the log - the dump that completed at 694645 ns printed
        // dev1 DEVCMDSTAT=0x10814B83, bit 8 (SETUP) SET, i.e. a SETUP landed
        // mid-dump and sat unserviced. Four USBDC1 control transfers were
        // ABORTED in that window, SET_CONFIGURATION never completed, and dev1
        // stayed unconfigured for the whole 3 ms run.
        //
        // Count-gating makes the dump rare in units of WORK rather than TIME,
        // which is what the reference does and why the reference survives.
        // The payload is also trimmed: no EP-list reads, short field names.
        if (poll_count % 2000 == 0 && poll_count > 0) {
            usb_select_device(0);
            VPRINTF(LOW, "MCU: [poll %d] hp=%d cyc=%d d0 armed=%d lb=%d "
                    "addr=%d | ",
                    poll_count, (int)dev0_hp_state, dev0_cycle_count,
                    (int)dev_state[0].ep1_armed,
                    (int)dev_state[0].loopback_armed,
                    usb_get_device_address());
            usb_select_device(1);
            VPRINTF(LOW, "d1 loops=%d armed=%d lb=%d addr=%d\n",
                    dev_state[1].loop_count, (int)dev_state[1].ep1_armed,
                    (int)dev_state[1].loopback_armed,
                    usb_get_device_address());
        }
    }

    if (dev1_isolation_violation) {
        VPRINTF(LOW, "MCU: USB DEV0 hotplug isolation test FAILED - USBDC1 was "
                "disturbed by USBDC0 connect/disconnect activity "
                "(dev0_cycles=%d dev1_loops=%d)\n",
                dev0_cycle_count, dev_state[1].loop_count);
    } else if (passed) {
        VPRINTF(LOW, "MCU: USB DEV0 hotplug isolation test PASSED - %d DEV0 "
                "connect/disconnect cycles with %d uninterrupted USBDC1 "
                "loopbacks\n",
                dev0_cycle_count, dev_state[1].loop_count);
    } else {
        VPRINTF(LOW, "MCU: USB DEV0 hotplug isolation test - TIMEOUT after "
                "%d us (hp_state=%d dev0_cycles=%d/%d dev1_loops=%d/%d "
                "polls=%d)\n",
                USB_TEST_RUN_BUDGET_US,
                (int)dev0_hp_state, dev0_cycle_count, DEV0_TARGET_CYCLES,
                dev_state[1].loop_count, DEV1_TARGET_LOOPS, poll_count);
    }

    VPRINTF(LOW, "MCU: USB dual-device HS DEV0 hotplug test - halting\n");
    csr_write_mpmc_halt();
}

// File contains AI-generated response based on internal company sources
