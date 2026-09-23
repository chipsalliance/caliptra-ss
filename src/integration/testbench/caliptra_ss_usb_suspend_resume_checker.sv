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
// caliptra_ss_usb_suspend_resume_checker
//
// Purpose
//   Give the caliptra_ss_usb_hs_dev_remote_wakeup test a DUT-side pass/fail
//   condition. Before this checker existed the test observed suspend and
//   resume only from the host side, by polling the VIP link state variable
//   from the stimulus sequence. That proves the VIP moved its own link state
//   machine; it proves nothing about the device under test. The firmware did
//   print a "Suspend change event" line when it saw DEVCMDSTAT.DSUS_C, but a
//   VPRINTF is read by no checker, so a build in which the DUT never noticed
//   the suspend at all still reported TESTCASE PASSED.
//
//   That gap matters specifically on this design. The MCU-owned device
//   controller USBDC0 now sits behind the on-chip 2-port hub, and a hub is
//   not obliged to propagate an upstream bus suspend down to a downstream
//   port: in a normal USB stack the host suspends an individual port by
//   sending SetPortFeature(PORT_SUSPEND) to the hub. So "does the downstream
//   device controller actually see suspend in this topology" is a real open
//   question about the DUT, and it is exactly the question the test was
//   silently failing to ask.
//
// What is observed
//   cptra_ss_usb_utmi_suspendm_o, the DUT UTMI+ SuspendM output. This is the
//   device controller telling the PHY to enter or leave its low-power state,
//   and it is the most direct DUT-side evidence available at testbench level
//   that the controller has recognised the bus condition:
//     SuspendM = 0  controller has entered suspend (active low)
//     SuspendM = 1  controller is running
//
//   Observing a DUT output pin is deliberate rather than reaching into the
//   register block hierarchically. The pin is already brought out to the
//   testbench and wired to the VIP at caliptra_ss_top_tb.sv, so this checker
//   needs no hierarchical path into third_party RTL and cannot break when a
//   pinned submodule is bumped.
//
// What is checked
//   CHK_SUSPEND_SEEN   The DUT must deassert SuspendM (drive it low) at some
//                      point during the observation window. If it never does,
//                      the device controller never entered suspend, and the
//                      suspend half of the test never happened regardless of
//                      what the VIP link state said. Evaluated when the
//                      stimulus closes its observation window.
//
//   CHK_RESUME_SEEN    Having entered suspend, the DUT must reassert SuspendM
//                      after the host drives resume K-state. If it enters
//                      suspend and never comes back the part is wedged, which
//                      previously showed up as a pass. Evaluated at the same
//                      point. Skipped, with an explicit message, when
//                      CHK_SUSPEND_SEEN already failed: there is no meaningful
//                      resume to check if suspend never happened, and emitting
//                      two errors for one root cause makes triage harder.
//
// Verdict integration
//   Failures use uvm_report_error, not $error. Only UVM report severities are
//   counted by caliptra_ss_usb_base_test::final_phase, which decides between
//   TESTCASE PASSED and TESTCASE FAILED. A plain $error would print and leave
//   the verdict at PASSED, which is the same class of bug this checker exists
//   to close.
//
//   Both checks are evaluated on a stimulus-driven event rather than a fixed
//   deadline. A wall-clock timeout would either fire before the firmware got
//   there (false failure) or sit past the end of simulation and never run at
//   all (silent pass on an unevaluated check). The sequence knows when its
//   observation window has closed; the checker asks it.
//
// Enabling
//   Inert unless +usb_suspend_resume_check is present on the simv command
//   line, so adding this module has no effect on any other test.
//   The stimulus sequence must trigger the global uvm_event named by
//   OBS_WINDOW_EVENT once its observation window closes, otherwise neither
//   check is ever evaluated.
//
// Progress reporting, and why this also saves runtime
//   As well as deciding the verdict, the checker announces each DUT reaction
//   on its own global uvm_event:
//     usb_dut_suspend_seen   triggered when SuspendM goes low
//     usb_dut_resume_seen    triggered when SuspendM goes high again
//
//   That lets the stimulus sequence wait for the DUT to actually react and
//   move on immediately, instead of dwelling for a fixed worst-case delay.
//   The original sequence sat on a hardcoded 2 ms suspend dwell plus a 500 us
//   post-resume wait, both paid unconditionally. Waiting on these events means
//   neither ceiling is paid in the passing case, and the dwell now ends because
//   the DUT responded rather than because a timer tuned on the legacy
//   single-device topology expired.
//
//   The remaining cost of the suspend half is protocol, not padding. Adding up
//   the terms that must elapse before the DUT can react: 500 us
//   LINK_SETTLE_DELAY, about 300 us of VIP inactivity timer, the DUT suspend
//   detection timer, and about 100 us of T_TWTRSTHS. With the spec suspend
//   detection value of 3.072 ms that is roughly 4.0 ms; with the sim-scaled
//   T_SUSPEND_DET of 200 us (G_SIM_CHIRP_TIMERS=1, which is how this testbench
//   elaborates the DUT) it is roughly 1.1 ms, so about a 3.5x to 4x reduction
//   on that half. No wall-clock figure is quoted here because no measured
//   baseline for this test has been recorded.

//
//   Events are used in preference to exposing the flags as module outputs so
//   that the sequence never needs a hierarchical path from the UVM package
//   into testbench scope.
//
// Arming, and why the edge detector cannot simply run from time zero
//   SuspendM is not a "device decided to suspend" flag, it is the PHY
//   low-power request. In usb_pie.m.vhdl the reset state BUS_EVENT_INIT drives
//   suspendm <= usbreg_pll_on or usbreg_dev_connect, so out of reset, before
//   firmware has written DEVCMDSTAT, SuspendM is legitimately 0: the PHY
//   clocks are held off because nothing is attached yet. When firmware later
//   writes PLL_ON / DEV_CONNECT in boot_usb_core, SuspendM rises.
//
//   A free-running edge detector therefore sees a complete low-then-high
//   sequence during boot, tens of microseconds before any stimulus exists.
//   That latched both flags, made the verdict a false PASS, and consumed the
//   full SUSPEND_DWELL and RESUME_WAIT_MAX ceilings in the sequence because
//   uvm_event::trigger() is momentary and had already fired before the
//   sequence started waiting.
//
//   The checker is therefore armed by the stimulus, on the global uvm_event
//   named by ARM_EVENT, which the sequence triggers only once the host has
//   stopped SOF traffic and the VIP link state machine has actually reached
//   SUSPENDED. Before that point no SuspendM activity is latched as an
//   observation. The edge history suspendm_prev is still tracked while
//   disarmed, so at the moment of arming it already holds the current level of
//   suspendm and the boot-time level can never be mistaken for an edge.
//
//   Gating on usbreg_dev_connect instead would not be enough: that signal
//   also goes high during boot, so the window would still open too early.
// -------------------------------------------------------------------------

module caliptra_ss_usb_suspend_resume_checker (
    input  logic utmi_clk,
    input  logic suspendm
);

    import uvm_pkg::*;

    string MSG_ID = "USB_SUSP_RES_CHK";

    // Name of the global uvm_event the stimulus sequence triggers when its
    // observation window closes. Must match the string used in
    // caliptra_ss_usb_hs_dev_remote_wakeup_sequence.svh.
    string OBS_WINDOW_EVENT = "usb_suspend_resume_obs_window_done";

    // Names of the global uvm_events this checker triggers to report DUT
    // reactions to the stimulus. Must match the strings used in
    // caliptra_ss_usb_hs_dev_remote_wakeup_sequence.svh.
    string DUT_SUSPEND_EVENT = "usb_dut_suspend_seen";
    string DUT_RESUME_EVENT  = "usb_dut_resume_seen";

    // Name of the global uvm_event the stimulus sequence triggers once it has
    // driven suspend and the VIP link reached SUSPENDED. See the header note
    // on arming. Must match the string used in the sequence.
    string ARM_EVENT = "usb_suspend_stimulus_armed";

    bit enabled;

    // Low until the stimulus arms this checker. While low the edge detector
    // ignores suspendm entirely, which is what keeps the boot-time PHY
    // clock-gating level out of the result.
    bit armed;

    // Latched observations. Not module outputs: see the header note on why the
    // sequence is told about these over uvm_events instead.
    bit suspend_seen;
    bit resume_seen;


    // Timestamps are kept for the report text only. Knowing when the DUT
    // reacted relative to the host stimulus is what makes a failure
    // diagnosable rather than just a boolean.
    realtime suspend_time;
    realtime resume_time;

    // Handles to the global events this checker triggers. Resolved once, in
    // the same initial block that samples the plusarg, so that the edge
    // detector below only has to call trigger(). uvm_event::trigger() is a
    // void function, so calling it from clocked logic is legal.
    uvm_event dut_suspend_seen_ev;
    uvm_event dut_resume_seen_ev;

    initial begin
        enabled = $test$plusargs("usb_suspend_resume_check");
        armed   = 1'b0;
        dut_suspend_seen_ev = uvm_event_pool::get_global(DUT_SUSPEND_EVENT);
        dut_resume_seen_ev  = uvm_event_pool::get_global(DUT_RESUME_EVENT);
        if (enabled) begin
            uvm_report_info(MSG_ID,

                $sformatf("enabled: watching DUT UTMI SuspendM, armed by event %s, completeness gated on event %s",
                          ARM_EVENT, OBS_WINDOW_EVENT),
                UVM_LOW);
        end
    end

    // ---------------------------------------------------------------------
    // Arming. See the header note: until the stimulus has driven suspend, the
    // SuspendM activity on this pin is boot-time PHY clock gating, not a DUT
    // response, and must not be latched.
    // ---------------------------------------------------------------------
    uvm_event arm_ev;

    // Edge history for the detector below. Written only by the clocked block
    // further down, which keeps tracking the SuspendM level even while the
    // checker is disarmed. Writing it from an initial block as well would be
    // an illegal combination of procedural drivers for an always_ff variable.
    logic suspendm_prev;

    initial begin
        // Let the plusarg sampling initial block above run first.
        #0;
        if (enabled) begin
            arm_ev = uvm_event_pool::get_global(ARM_EVENT);
            arm_ev.wait_trigger();
            // The edge history is maintained by the clocked block even while
            // disarmed, so whatever level SuspendM happens to sit at when the
            // window opens cannot itself be reported as an edge.
            armed = 1'b1;
            uvm_report_info(MSG_ID,
                $sformatf("armed: now watching DUT UTMI SuspendM (current level %0b)", suspendm),
                UVM_LOW);
        end
    end

    // ---------------------------------------------------------------------
    // Edge detection on the DUT SuspendM output.
    //
    // SuspendM is active low: the controller drives it to 0 to put the PHY
    // into its low-power state. Resume is only counted after a suspend has
    // been seen, so that the initial power-up value of the pin cannot be
    // mistaken for a resume event.
    // ---------------------------------------------------------------------
    always_ff @(posedge utmi_clk) begin
        if (!enabled || !armed) begin
            // Pre-arm SuspendM activity is never latched as an observation.
            // Only the edge history is tracked, so that the level present when
            // the window opens cannot later be reported as an edge.
            suspendm_prev <= suspendm;
        end
        else begin
            // Falling edge: controller entered suspend.
            if (suspendm_prev === 1'b1 && suspendm === 1'b0 && !suspend_seen) begin
                suspend_seen <= 1'b1;
                suspend_time <= $realtime;
                uvm_report_info(MSG_ID,
                    "CHK_SUSPEND_SEEN: DUT deasserted UTMI SuspendM, device controller entered suspend",
                    UVM_LOW);
                // Release the stimulus from its suspend dwell as soon as the
                // DUT has actually reacted, instead of waiting out the
                // worst-case SUSPEND_DWELL ceiling.
                dut_suspend_seen_ev.trigger();
            end

            // Rising edge after a suspend: controller resumed.

            if (suspendm_prev === 1'b0 && suspendm === 1'b1
                && suspend_seen && !resume_seen) begin
                resume_seen <= 1'b1;
                resume_time <= $realtime;
                uvm_report_info(MSG_ID,
                    "CHK_RESUME_SEEN: DUT reasserted UTMI SuspendM, device controller resumed",
                    UVM_LOW);
                // Release the stimulus from its post-resume wait.
                dut_resume_seen_ev.trigger();
            end


            suspendm_prev <= suspendm;
        end
    end

    // ---------------------------------------------------------------------
    // Verdict, evaluated when the stimulus closes its observation window.
    // ---------------------------------------------------------------------
    uvm_event obs_window_done;

    initial begin
        // Let the plusarg sampling initial block above run first.
        #0;
        if (enabled) begin
            obs_window_done = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
            obs_window_done.wait_trigger();

            if (!suspend_seen) begin
                uvm_report_error(MSG_ID,
                    "CHK_SUSPEND_SEEN FAILED: the DUT never deasserted UTMI SuspendM during the observation window. The host stopped SOF traffic and the VIP link reached SUSPENDED, but the device controller behind the hub never entered suspend, so the suspend half of this test did not exercise the DUT at all. Most likely the on-chip hub is not propagating the upstream bus suspend to its downstream port, which in a normal USB stack is done per port with SetPortFeature(PORT_SUSPEND) rather than implicitly.");
                uvm_report_info(MSG_ID,
                    "CHK_RESUME_SEEN SKIPPED: not evaluated because no suspend was ever observed.",
                    UVM_LOW);
            end
            else if (!resume_seen) begin
                uvm_report_error(MSG_ID,
                    $sformatf("CHK_RESUME_SEEN FAILED: the DUT entered suspend at %0t (UTMI SuspendM low) but never reasserted SuspendM before the observation window closed. The host drove resume K-state via the link service clear_suspend sequence and restarted SOF, so the device controller should have left its low-power state. It is still suspended.",
                              suspend_time));
            end
            else begin
                uvm_report_info(MSG_ID,
                    $sformatf("CHK_SUSPEND_SEEN and CHK_RESUME_SEEN PASSED: DUT entered suspend at %0t and resumed at %0t, so the device controller behind the hub did observe both the upstream suspend and the host resume.",
                              suspend_time, resume_time),
                    UVM_LOW);
            end
        end
    end

endmodule
