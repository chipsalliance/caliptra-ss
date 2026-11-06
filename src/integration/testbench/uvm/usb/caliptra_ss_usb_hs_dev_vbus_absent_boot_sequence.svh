// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_HS_DEV_VBUS_ABSENT_BOOT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_VBUS_ABSENT_BOOT_SEQUENCE_SV

// =============================================================================
// USB High-Speed "VBus absent at boot" sequence.
//
// GOAL
//   Prove the compound device boots, enables its hub and requests an upstream
//   connect with NO host present, stays silent on the bus while that is true,
//   and then attaches and enumerates correctly at HS once the host finally
//   appears. This is the normal self-powered-device case - the SoC has its own
//   supply and boots whether or not a cable is plugged in - and no other test
//   in the suite exercises it.
//
// HOW THE "NO HOST" WINDOW IS CREATED
//   Not by a testbench force. VBus already starts at 0 in every run: the VIP
//   drives utmi_dut_mac_if.VbusValid = 0 in the first delta and
//   caliptra_ss_usb_vbus_driver.sv forwards that to the DUT pin. What normally
//   hides this scenario is only the TIMING - the VIP's own auto-attach raises
//   VBus at 20 us (poweron_auto_attach_delay in caliptra_ss_usb_shared_cfg),
//   which is ~12 us before firmware even touches the USB core.
//
//   The companion test class therefore just moves that auto-attach out to
//   VBUS_ATTACH_DELAY_US. The VIP then performs the VBus rise itself at that
//   time and the existing vbus driver forwards it. No plusarg, no force, no
//   two-sided handshake.
//
// WHY THE NEGATIVE WINDOW IS THE INTERESTING PART
//   Per ip_xxx_3511_hs_mem_compound_structure.a.vhdl:2103
//       hub_connect <= sync_VBusDebounced and hub_dcon_q
//   so firmware setting HUB_EN|HUB_CONNECT cannot by itself put the hub on
//   the bus. Step 2 below asserts the host side of that: the VIP link must
//   never reach ENABLED while VBus is still low. The firmware checks the
//   device side (VBUS_DEBOUNCED stays 0 across the HUB_CONNECT write).
//
// SEQUENCE FLOW
//   1. Do NOT start SOF. Do nothing at all - firmware is booting into a dead
//      bus and that is the point.
//   2. Negative window: for NEGATIVE_WINDOW_US, assert the link never reaches
//      ENABLED. Firmware reaches HUB_CONNECT at 55-70 us (measured), so this
//      window must outlast that and close before the VIP auto-attach.
//   3. Wait past the scheduled auto-attach time, then start SOF generation.
//   4. Wait for the link to reach ENABLED - the first genuine attach.
//   5. Hub-aware enumeration via enumerate_hub_and_usbdc0(): hub at address
//      1, hub-class bring-up of downstream port 1, USBDC0 at address 2.
//
// PASS CRITERION / WHY THERE IS NO EP1 TRAFFIC HERE
//   The verdict is the conjunction of three things:
//     - this sequence's negative window (the host sees nothing on the bus
//       while VBus is low),
//     - the full hub-aware enumeration completing, which only succeeds if
//       firmware is servicing real SETUP tokens forwarded through the hub,
//     - the firmware's own post-enumeration assertion that
//       DEVCMDSTAT.SPEED == HS.
//   No EP1 data transfer is issued. The companion firmware is an EP0-only
//   event loop: unlike the bulk_loopback firmware it has no EP1 OUT -> IN
//   copy handler, so a bulk transfer here would never be answered and would
//   only produce a spurious timeout. Endpoint traffic after a late attach
//   belongs in a follow-up test paired with loopback-capable firmware.
//
// Note on the speed check: it lives in firmware rather than here because
// DEVCMDSTAT.SPEED is the authoritative negotiated-speed status. A late
// attach is exactly the case where a missed chirp would silently leave the
// link at FS, since usb_pie's BUS_EVENT_INIT path asserts set_dev_fs.
// =============================================================================

class caliptra_ss_usb_hs_dev_vbus_absent_boot_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_vbus_absent_boot_sequence)

    // Length of the "host must stay away" assertion window, in us.
    //
    // Must satisfy: max(HUB_CONNECT time) < NEGATIVE_WINDOW_US < attach time.
    // Measured across 41 HS runs of caliptra_nightly_regression_2026_10_24_-
    // 05_31_55, firmware reaches usb_hub_connect() between 55.3 us and
    // 69.5 us (the late cluster being the descriptor-override family). The
    // test class attaches at 150 us. 130 us sits above the worst observed
    // HUB_CONNECT with 60 us of margin and closes 20 us before the attach, so
    // the window never overlaps the attach edge.
    int unsigned negative_window_us = 130;

    // Must match VBUS_ATTACH_DELAY_US in
    // caliptra_ss_usb_hs_dev_vbus_absent_boot_test.svh. Used to decide how
    // long to wait for the VBus rise before giving up.
    int unsigned vbus_attach_delay_us = 150;

    // Margin added after the scheduled attach time before SOF is started, to
    // be certain the VBus rise has been taken by the vbus driver and the DUT
    // has debounced it. Measured: the VIP raises VBus at exactly
    // vbus_attach_delay_us and firmware observes VBUS_DEBOUNCED about 2.9 us
    // later, so 20 us is ample.
    int unsigned vbus_attach_margin_us = 20;

    // Upper bound on the post-attach link wait. Same rationale as elsewhere:
    // an unbounded wait turns a dead link into an opaque MCU-halt timeout.
    int unsigned link_up_timeout_us = 3000;

    // Settling delay between the link reaching ENABLED and the first SETUP.
    // The host bus reset makes firmware take the DRES_C path
    // (usb_handle_bus_reset() -> usb_ep0_reinit()), and EP0 must be re-armed
    // before a token arrives or the first control transfer is lost. Same
    // 50 us the bulk_loopback sequences use after their port reset.
    int unsigned post_reset_settle_us = 50;

    function new(string name = "caliptra_ss_usb_hs_dev_vbus_absent_boot_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Assert the host link stays out of ENABLED for the whole window.
    //
    // Implemented as a race between a timer and a state watcher rather than by
    // sampling at the end, because the failure of interest is transient: a
    // spurious attach could bring the link up and drop it again inside the
    // window, and an end-of-window sample would miss that entirely.
    // -------------------------------------------------------------------------
    protected task assert_link_stays_down(svt_usb_status shared_status,
                                          int unsigned  window_us,
                                          string        label);
        bit came_up;

        came_up = 1'b0;

        `uvm_info("USB_VBUS_ABSENT_SEQ",
            $sformatf({"Negative window: asserting the link stays out of ",
                       "ENABLED for %0d us while VBus is absent (%s). ",
                       "Current state=%p."},
                      window_us, label, shared_status.link_usb_20_state),
            UVM_LOW)

        fork
            begin : WATCH_LINK
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                came_up = 1'b1;
                disable WINDOW_TIMER;
            end
            begin : WINDOW_TIMER
                #(window_us * 1us);
                disable WATCH_LINK;
            end
        join

        if (came_up) begin
            `uvm_error("USB_VBUS_ABSENT_SEQ",
                $sformatf({"Link reached ENABLED at %0t, while VBus should ",
                           "still be absent (%s). The hub connected upstream ",
                           "without VBus, which contradicts ",
                           "hub_connect <= sync_VBusDebounced and hub_dcon_q. ",
                           "Either the VIP auto-attach fired earlier than the ",
                           "configured %0d us, or the hub's VBus gating is ",
                           "broken."},
                          $realtime, label, vbus_attach_delay_us))
        end
        else begin
            `uvm_info("USB_VBUS_ABSENT_SEQ",
                $sformatf({"Negative window passed: link stayed at %p for the ",
                           "full %0d us. Firmware's HUB_CONNECT did not put ",
                           "the hub on the bus."},
                          shared_status.link_usb_20_state, window_us),
                UVM_LOW)
        end
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        // -----------------------------------------------------------------
        // Step 1 + 2: Stay off the bus and assert the DUT does too.
        //
        // Deliberately no start_sof_generation() here. The host is modelled
        // as simply not being there yet: no VBus (the VIP has not attached),
        // and no frames.
        // -----------------------------------------------------------------
        assert_link_stays_down(shared_status, negative_window_us,
                               "firmware boots + HUB_EN + HUB_CONNECT");

        // -----------------------------------------------------------------
        // Step 3: The host arrives.
        //
        // The VIP raises VBus on its own at vbus_attach_delay_us via
        // poweron_auto_attach_delay; nothing is driven here. Simply wait
        // until that scheduled time has passed, then start frames.
        //
        // Why a plain delay and not a wait on the link state: before the
        // attach the VIP host link sits in DISCONNECTED, NOT POWERED_OFF. An
        // earlier revision waited for "state != POWERED_OFF" as evidence of
        // the attach, which was already true on entry - so it fell through
        // immediately at 130 us, logged "VBus arrived" 20 us before the rise
        // actually happened, and its sibling timeout branch then fired a
        // spurious "VIP never attached" error at 680 us. There is no link
        // state that cleanly marks "VBus is now up" here, and none is needed:
        // the rise is at a time we chose ourselves, and the real evidence
        // that the attach worked is the link reaching ENABLED in Step 4,
        // which is already bounded and already reports loudly on failure.
        //
        // SOF is started only after the attach, so the link has something to
        // keep it alive once it reaches ENABLED. Starting it during the
        // negative window would be driving frames at a device that is not
        // attached.
        // -----------------------------------------------------------------
        if ($realtime < (vbus_attach_delay_us + vbus_attach_margin_us) * 1us)
            #((vbus_attach_delay_us + vbus_attach_margin_us) * 1us - $realtime);

        `uvm_info("USB_VBUS_ABSENT_SEQ",
            $sformatf({"Past the scheduled VIP auto-attach (%0d us + %0d us ",
                       "margin); link state is now %p. Starting SOF."},
                      vbus_attach_delay_us, vbus_attach_margin_us,
                      shared_status.link_usb_20_state),
            UVM_LOW)

        start_sof_generation();

        // -----------------------------------------------------------------
        // Step 4: First genuine link-up.
        //
        // The hub has been asking to connect since ~70 us, so hub_connect
        // asserts as soon as VBus debounces. The host then drives reset and
        // HS chirp with no further firmware action.
        // -----------------------------------------------------------------
        wait_for_link_enabled(shared_status,
                              "HS host link (first attach after late VBus)",
                              link_up_timeout_us);
        if (link_wait_timed_out)
            return;

        // Let firmware finish servicing the attach bus reset (DRES_C ->
        // usb_handle_bus_reset() -> usb_ep0_reinit()) and re-arm EP0 before
        // the first SETUP token is driven.
        #(post_reset_settle_us * 1us);

        // -----------------------------------------------------------------
        // Step 5: Hub-aware enumeration.
        //
        // Must be hub-aware: the hub answers all control traffic at address
        // 0 out of its own descriptor array and never forwards a SETUP to
        // USBDC0 until the hub itself is enumerated AND downstream port 1
        // has been brought up with hub-class requests. A flat
        // GET_DESCRIPTOR/SET_ADDRESS/SET_CONFIGURATION enumeration appears
        // to succeed on the host side while firmware sees zero SETUPs.
        // -----------------------------------------------------------------
        enumerate_hub_and_usbdc0(
            .host_agent_h (host_agent_h),
            .usb_cfg      (usb_cfg),
            .suffix       ("_after_vbus"));

        `uvm_info("USB_VBUS_ABSENT_SEQ",
            "Enumeration complete after late VBus arrival.", UVM_LOW)

        // Give firmware time to run its post-enumeration checks (the
        // DEVCMDSTAT.SPEED == HS assertion) and print its verdict line while
        // the run phase is still active, so a FAIL is turned into a
        // UVM_ERROR by caliptra_ss_mcu_console_fail_checker rather than
        // being lost at teardown.
        #50us;

        `uvm_info("USB_VBUS_ABSENT_SEQ",
            {"VBus-absent-at-boot sequence complete: the hub stayed off the ",
             "bus while VBus was absent, then attached, reset, chirped and ",
             "enumerated once the host arrived."},
            UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_VBUS_ABSENT_BOOT_SEQUENCE_SV
