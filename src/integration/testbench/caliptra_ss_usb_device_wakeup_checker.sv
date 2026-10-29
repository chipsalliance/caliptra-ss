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
// -------------------------------------------------------------------------
// caliptra_ss_usb_device_wakeup_checker
//
// Purpose
//   Own the pass/fail decision for DEVICE-INITIATED remote wakeup, by watching
//   the DUT drive resume K upstream on the UTMI+ pins.
//
//   Remote wakeup is device-initiated and host-completed, and the two halves
//   must be checked in different places:
//
//     device half  MCU firmware writes DEVCMDSTAT to set usbreg_remotewakeup,
//                  and the peripheral engine drives K upstream for T_3ms. This
//                  is the DUT feature under test and it is what this checker
//                  observes. Only the device can produce it.
//
//     host half    the host must take over resume signalling within 1 ms of
//                  that K and terminate it with a low-speed EOP, i.e. an SE0
//                  (USB 2.0 section 7.1.7.7). The device cannot resume the bus
//                  by itself: usb_pie.m.vhdl BUS_EVENT_SW_WAKEUP_3 waits for
//                  SE0 with no timer and no other exit arc, so it parks there
//                  until the host closes the handshake. Driving that host half
//                  is the stimulus sequence's job, and it must happen only
//                  AFTER this checker has latched, or the test could pass on a
//                  device that never woke at all.
//
// Why this is not checked from the host VIP
//   The obvious host-side observable, svt_usb_status::device_remote_wakeup_in_progress,
//   was measured staying 0 through a full, correct, 3.089 ms device K: see
//   docs/usb_remote_wakeup_selfclear_race_report.md sections 2A.4 and 7.4. The
//   most probable reason is that the VIP only latches it once it observes a
//   COMPLETE device resume, including the host takeover it expects to perform
//   itself, so it can never be satisfied by the device half alone. Rather than
//   reverse-engineer closed VIP source, the check was moved to the pins, where
//   the evidence is unambiguous and was already confirmed by hand.
//
// What is observed
//   txvalid   cptra_ss_usb_utmi_txvalid_o, a DUT OUTPUT. This is what makes the
//             check specific to the device: a host-driven resume K appears on
//             linestate too, but it is not accompanied by the DUT asserting
//             TXValid. Requiring both means nothing the host or the VIP does
//             can satisfy this checker.
//   linestate cptra_ss_usb_utmi_linestate_i. At full speed idle J is 2'b01 and
//             K is 2'b10, so K is the inverted-from-idle state that resume
//             signalling uses. Measured as 2'b10 for the whole device K in the
//             run analysed in the report.
//
// What is checked
//   CHK_DEVICE_WAKEUP_K  While armed, the DUT must assert TXValid with
//                        linestate = K continuously for at least K_MIN_HOLD.
//                        Evaluated when the stimulus closes its observation
//                        window, on the same event the suspend/resume checker
//                        uses.
//
//   The minimum hold requirement is what keeps this from latching on an
//   unrelated transmit that happens to leave linestate at K for a few cycles.
//   It is generously satisfiable: the device drives resume K for T_3ms, i.e.
//   3.072 ms nominal and 3.089 ms measured, which is over a hundred times
//   K_MIN_HOLD.
//
// Why detection is polled and not clocked
//   Same reason as caliptra_ss_usb_suspend_resume_checker: the device requests
//   the wakeup while the PHY is still in low power, and in this testbench
//   utmi_clk comes from the VIP MAC interface, so a clocked detector can be
//   starved of edges across exactly the interval of interest. A polling loop
//   needs no clock. The accumulate-and-reset form also gives the sustained-hold
//   requirement for free.
//
// Arming
//   Shares ARM_EVENT with caliptra_ss_usb_suspend_resume_checker, so a sequence
//   that already arms that checker arms this one too, at the same point: after
//   boot and before the suspend stimulus. Nothing before arming is latched.
//
// Progress reporting
//   Triggers the global uvm_event usb_dut_wakeup_k_seen as soon as the hold is
//   satisfied. That is the sequence's cue that the device half is done and that
//   it may now drive the host half. It is a uvm_event rather than a module
//   output so the sequence needs no hierarchical path from the UVM package into
//   testbench scope.
//
// Verdict integration
//   uvm_report_error, not $error: only UVM report severities are counted by
//   caliptra_ss_usb_base_test::final_phase when it decides PASSED versus
//   FAILED.
//
// Enabling
//   Inert unless +usb_device_wakeup_check is present on the simv command line,
//   so adding this module has no effect on any other test. It is a separate
//   plusarg from +usb_suspend_resume_check because global-suspend tests, where
//   the host ends the suspend and the device never signals wakeup, must not
//   acquire a check they are guaranteed to fail.
// -------------------------------------------------------------------------

module caliptra_ss_usb_device_wakeup_checker (
    input  logic       utmi_clk,
    input  logic       txvalid,
    input  logic [1:0] linestate
);

    import uvm_pkg::*;

    string MSG_ID = "USB_DEV_WAKEUP_CHK";

    // Full-speed K state on the UTMI linestate encoding. Idle J is 2'b01.
    localparam bit [1:0] LINESTATE_K = 2'b10;

    // Polling step and the sustained-hold requirement. K_MIN_HOLD must stay far
    // below the T_3ms device K (3.072 ms) and far above any incidental transmit
    // that could leave linestate at K.
    localparam realtime POLL_STEP = 1us;
    localparam realtime K_MIN_HOLD = 20us;

    // Event names. Duplicated verbatim in the stimulus sequence, because a
    // uvm_sequence cannot reach into testbench scope and this checker must not
    // depend on the UVM test package. Keep both copies in sync.
    string OBS_WINDOW_EVENT = "usb_suspend_resume_obs_window_done";
    string ARM_EVENT        = "usb_suspend_stimulus_armed";
    string WAKEUP_K_EVENT   = "usb_dut_wakeup_k_seen";

    bit enabled;
    bit armed;

    // Latched observation, plus the timestamp and hold length for the report
    // text. A failure that says only "no" is much harder to triage than one
    // that can say how long the K actually lasted.
    bit      wakeup_k_seen;
    realtime wakeup_k_time;
    realtime wakeup_k_hold;

    // Longest hold observed even if it never reached K_MIN_HOLD. This is the
    // difference between "the device never drove K at all" and "the device
    // drove K but only briefly", which point at different defects.
    realtime longest_hold;

    uvm_event wakeup_k_seen_ev;
    uvm_event arm_ev;
    uvm_event obs_window_done;

    initial begin
        enabled       = $test$plusargs("usb_device_wakeup_check");
        armed         = 1'b0;
        wakeup_k_seen = 1'b0;
        longest_hold  = 0;
        wakeup_k_seen_ev = uvm_event_pool::get_global(WAKEUP_K_EVENT);
        if (enabled) begin
            uvm_report_info(MSG_ID,
                $sformatf("enabled: watching DUT UTMI TXValid with linestate=K for a sustained %0t, armed by event %s, verdict gated on event %s",
                          K_MIN_HOLD, ARM_EVENT, OBS_WINDOW_EVENT),
                UVM_LOW);
        end
    end

    // ---------------------------------------------------------------------
    // Arming. Shares the suspend/resume checker's arm event.
    // ---------------------------------------------------------------------
    initial begin
        // Let the plusarg sampling initial block above run first.
        #0;
        if (enabled) begin
            arm_ev = uvm_event_pool::get_global(ARM_EVENT);
            arm_ev.wait_trigger();
            armed = 1'b1;
            uvm_report_info(MSG_ID,
                "armed: now watching for device-driven resume K on the UTMI pins",
                UVM_LOW);
        end
    end

    // ---------------------------------------------------------------------
    // Detection. Accumulate while the device is driving K, reset on any break,
    // latch once the accumulated hold reaches K_MIN_HOLD.
    // ---------------------------------------------------------------------
    realtime hold_acc;

    initial begin
        #0;
        if (enabled) begin
            hold_acc = 0;
            forever begin
                #POLL_STEP;
                if (armed && (txvalid === 1'b1) && (linestate === LINESTATE_K)) begin
                    hold_acc = hold_acc + POLL_STEP;
                    if (hold_acc > longest_hold) longest_hold = hold_acc;
                    if (!wakeup_k_seen && (hold_acc >= K_MIN_HOLD)) begin
                        wakeup_k_seen = 1'b1;
                        // Back-date to where the hold began, which is the
                        // meaningful timestamp for correlating against the
                        // firmware's DEVCMDSTAT write.
                        wakeup_k_time = $realtime - hold_acc;
                        wakeup_k_hold = hold_acc;
                        uvm_report_info(MSG_ID,
                            $sformatf("CHK_DEVICE_WAKEUP_K: DUT drove resume K upstream (TXValid high, linestate=K) from %0t, sustained %0t. This is device-initiated remote wakeup on the wire. The host must now take over the resume and terminate it with an EOP, or the device parks in BUS_EVENT_SW_WAKEUP_3.",
                                      wakeup_k_time, hold_acc),
                            UVM_LOW);
                        wakeup_k_seen_ev.trigger();
                    end
                end
                else begin
                    hold_acc = 0;
                end
            end
        end
    end

    // ---------------------------------------------------------------------
    // Verdict, evaluated when the stimulus closes its observation window.
    // ---------------------------------------------------------------------
    initial begin
        // Let the plusarg sampling initial block above run first.
        #0;
        if (enabled) begin
            obs_window_done = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
            obs_window_done.wait_trigger();

            if (wakeup_k_seen) begin
                uvm_report_info(MSG_ID,
                    $sformatf("CHK_DEVICE_WAKEUP_K PASSED: device-driven resume K observed at %0t on the DUT UTMI pins.",
                              wakeup_k_time),
                    UVM_LOW);
            end
            else if (longest_hold == 0) begin
                uvm_report_error(MSG_ID,
                    "CHK_DEVICE_WAKEUP_K FAILED: the DUT never once asserted UTMI TXValid with linestate=K while armed, so it never drove resume K upstream and device-initiated remote wakeup did not happen. Check, in this order: that the firmware called usb_allow_clock_stop() so the controller could suspend at all; that DEVCMDSTAT.DSUS was set when usb_request_remote_wakeup() wrote the request, since usbreg_remotewakeup is only acted on from a suspended state and is not latched; and that the checker was armed before the request was issued.");
            end
            else begin
                uvm_report_error(MSG_ID,
                    $sformatf("CHK_DEVICE_WAKEUP_K FAILED: the DUT did drive UTMI TXValid with linestate=K, but never for the required %0t; the longest continuous hold was %0t. The wakeup was started and abandoned rather than never attempted, so look at the peripheral engine leaving BUS_EVENT_SW_WAKEUP_1 early rather than at the firmware request path.",
                              K_MIN_HOLD, longest_hold));
            end
        end
    end

endmodule

// File contains AI-generated response based on internal company sources
