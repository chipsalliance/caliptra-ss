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
// caliptra_ss_usb_fs_speed_checker
//
// Purpose
//   Prove that the USB link is actually operating at Full Speed (12 Mbit/s)
//   rather than High Speed (480 Mbit/s), by observing the UTMI+ interface
//   between the DUT USB controller and the USB VIP PHY.
//
// Why this checker does not measure a clock
//   An earlier revision of the caliptra_ss_usb_fs_clock test claimed that a
//   checker bound to the AST clk_src_usb_o net measured the USB clock and
//   proved FS operation. That approach is not implementable and would not
//   prove anything even if it were:
//     1. The AST module is not part of this testbench. Only src/ast/rtl/
//        ast_pkg.sv is compiled; ast.sv, ast_clks_byp.sv and usb_clk.sv are
//        not in caliptra_ss_top_tb.vf and no ast instance exists, so there is
//        no clk_src_usb_o net in the elaborated design.
//     2. The UTMI clock rate does not encode the link speed. The testbench
//        generates a 60 MHz usb_utmi_clk (USB_UTMI_CLK_PERIOD = 16667ps), and
//        the VIP generates its own UTMI interface clock which has been observed
//        at 48 MHz (the UTMI+ FS-only 8-bit option). Neither frequency is a
//        function of whether the link negotiated HS or FS: the same clock rate
//        is used for both. USB speed is encoded in the protocol and in the PHY
//        speed-select pins, so measuring any clock in this testbench can never
//        distinguish HS from FS.
//
// What is actually checked
//   CHK_XCVR_FS      PHY speed selection. On the first received packet the
//                    DUT must be driving XcvrSelect = 1 and TermSelect = 1
//                    (UTMI+ FS transceiver plus FS termination). If the chirp
//                    handshake had succeeded into HS both would be 0.
//
//   CHK_RATE_FS      Actual line rate. In UTMI+ 8-bit mode the PHY asserts
//                    RXValid once per received byte, so the RXValid-to-RXValid
//                    interval during an active packet is a direct measurement
//                    of the line rate:
//                        byte period = 8 bits / line rate
//                      HS  480 Mbit/s -> byte period   16.67 ns
//                      FS   12 Mbit/s -> byte period  666.67 ns
//
//                    The interval is measured in SIMULATION TIME, not in UTMI
//                    clock counts, and this is deliberate. Counting clocks
//                    requires knowing the UTMI clock frequency, and that
//                    frequency is not fixed here: the checker observes
//                    usb_20_mac_if.utmi_dut_mac_if.CLK, which the VIP generates
//                    itself (generate_clk = 1) rather than the testbench 60 MHz
//                    usb_utmi_clk. An earlier revision of this checker assumed
//                    60 MHz and therefore expected 40 clocks per FS byte, but
//                    measured 32 on a known-good FS link. 32 clocks is not an
//                    error: 32 x 20.833 ns is exactly 666.7 ns, i.e. the VIP is
//                    driving the UTMI clock at 48 MHz, which is the UTMI+
//                    FS-only 8-bit interface option. Measuring time instead of
//                    clocks makes the check correct for 60 MHz, 48 MHz, or any
//                    other clock the VIP may choose. The clock period is still
//                    measured and reported, for diagnostics only.
//
//                    The statistic used is the MAXIMUM interval observed, not
//                    the average. Packet framing produces occasional intervals
//                    SHORTER than the steady-state byte period (for example
//                    the gap between RXActive rising and the first payload
//                    byte), so an average is biased low. Contamination is
//                    one-directional, so the maximum recovers the true byte
//                    period. High Speed can never produce a long interval, so
//                    the check still separates the two speeds cleanly.
//
//   CHK_SOF_PERIOD   Optional, off by default. FS frame interval is 1 ms
//                    (HS microframe interval is 125 us). Enabling this
//                    requires the test to observe the bus for several
//                    milliseconds, which costs simulation time, so it is
//                    gated behind its own plusarg.
//
//   CHK_SAW_TRAFFIC  Liveness and completeness. Evaluated when the stimulus
//                    sequence signals that its observation window has closed,
//                    via the global uvm_event named below. If no packet was
//                    ever received the link never came up; if traffic started
//                    but CHK_RATE_FS never gathered enough samples, the rate
//                    was never actually confirmed. Either way the test must
//                    fail rather than report a pass on unevaluated checks.
//
// Verdict integration
//   Failures are reported with uvm_report_error, not $error. Only UVM report
//   severities are counted by caliptra_ss_usb_base_test::final_phase, which
//   decides between TESTCASE PASSED and TESTCASE FAILED. A plain $error would
//   print but leave the verdict at PASSED.
//
// Enabling
//   The whole checker is inert unless +usb_fs_speed_check is present on the
//   simv command line, so adding this module has no effect on any other test.
//     +usb_fs_speed_check                     enable CHK_XCVR_FS, CHK_RATE_FS,
//                                             CHK_SAW_TRAFFIC
//     +usb_fs_sof_check                       additionally enable CHK_SOF_PERIOD
//
//   The completeness guard is event driven, not time driven, so there is no
//   deadline plusarg. The stimulus sequence must trigger the global uvm_event
//   named by OBS_WINDOW_EVENT when its observation window closes.
// -------------------------------------------------------------------------

module caliptra_ss_usb_fs_speed_checker (
    input  logic       utmi_clk,
    input  logic       utmi_reset,
    input  logic       rxactive,
    input  logic       rxvalid,
    input  logic [7:0] rxdata,
    input  logic       xcvrselect,
    input  logic       termselect,
    input  logic [1:0] opmode,
    input  logic [1:0] linestate
);

    import uvm_pkg::*;

    // ---------------------------------------------------------------------
    // Expected RXValid-to-RXValid interval, in simulation time, for each speed.
    // A byte is 8 bit periods, so the byte period is 8 / line_rate:
    //   FS 12 Mbit/s  -> 8 / 12e6  = 666.67 ns
    //   HS 480 Mbit/s -> 8 / 480e6 =  16.67 ns
    // The tolerance is wide because the value only has to separate FS from HS,
    // and those differ by a factor of 40. It is deliberately NOT expressed in
    // UTMI clock counts: see the CHK_RATE_FS note in the file header.
    // ---------------------------------------------------------------------
    localparam realtime FS_BYTE_PERIOD_MIN = 600ns;
    localparam realtime FS_BYTE_PERIOD_MAX = 740ns;

    // Number of RXValid-to-RXValid intervals to collect before deciding.
    // A Full Speed SOF token carries only a PID plus two frame-number bytes,
    // so a single short packet yields just two or three RXValid intervals.
    // Requiring more than this makes the rate check silently never evaluate on
    // a SOF-only link, which would leave the test vacuous.
    localparam int unsigned RATE_SAMPLES_NEEDED = 2;

    // FS frame interval is 1 ms. Allow a generous window: the VIP schedules
    // SOFs from its own frame timer and the first interval after link-up can
    // be short.
    localparam realtime SOF_PERIOD_FS_MIN = 900us;
    localparam realtime SOF_PERIOD_FS_MAX = 1100us;

    localparam logic [7:0] USB_PID_SOF = 8'hA5;

    string MSG_ID = "USB_FS_SPEED_CHK";

    // Name of the global uvm_event the stimulus sequence triggers when its
    // observation window closes. Must match the string used in
    // caliptra_ss_usb_fs_clock_sequence.svh.
    string OBS_WINDOW_EVENT = "usb_fs_obs_window_done";

    bit enabled;
    bit sof_check_enabled;

    initial begin
        enabled           = $test$plusargs("usb_fs_speed_check");
        sof_check_enabled = $test$plusargs("usb_fs_sof_check");
        if (enabled) begin
            // Times are formatted by hand in nanoseconds rather than with %0t.
            // This initial block runs at time 0, before the VIP has called
            // $timeformat, so %0t here would print raw timescale units and be
            // unreadable.
            uvm_report_info(MSG_ID,
                $sformatf("enabled: expecting FS RXValid byte period between %0.1f ns and %0.1f ns, completeness gated on event %s, sof_check=%0b",
                          FS_BYTE_PERIOD_MIN / 1ns, FS_BYTE_PERIOD_MAX / 1ns,
                          OBS_WINDOW_EVENT, sof_check_enabled),
                UVM_LOW);

        end
    end

    // ---------------------------------------------------------------------
    // Packet framing: a packet is the interval where rxactive is high. The
    // first RXValid byte inside it is the PID.
    // ---------------------------------------------------------------------
    bit          in_packet;
    bit          pid_captured;
    logic [7:0]  pid;
    int unsigned bytes_this_packet;
    bit          saw_any_packet;

    // Rate measurement state. Intervals are held as simulation time, so the
    // measurement does not depend on the UTMI clock frequency.
    realtime     last_rxvalid_time;
    bit          have_prev_rxvalid;
    int unsigned spacing_samples;
    realtime     byte_period_max;
    bit          rate_checked;

    // UTMI clock period, measured at runtime for diagnostics only. Reported
    // alongside the rate result so a future frequency change is obvious in the
    // log rather than showing up as a mysterious rate failure.
    realtime     utmi_clk_prev_edge;
    realtime     utmi_clk_period;

    // PHY speed-select check state.
    bit          xcvr_checked;

    // SOF timing state.
    realtime     last_sof_time;
    bit          have_last_sof;
    bit          sof_period_checked;

    always_ff @(posedge utmi_clk) begin
        if (!enabled) begin
            // Nothing to do. Keep the block trivially inert so that disabled
            // runs cost no simulation work beyond the clock sensitivity.
        end
        else begin
            // --- UTMI clock period measurement (diagnostics only) ---
            if (utmi_clk_prev_edge != 0.0) begin
                utmi_clk_period <= $realtime - utmi_clk_prev_edge;
            end
            utmi_clk_prev_edge <= $realtime;

            // --- packet framing ---
            if (rxactive && !in_packet) begin
                in_packet         <= 1'b1;
                pid_captured      <= 1'b0;
                bytes_this_packet <= 0;
                have_prev_rxvalid <= 1'b0;
            end
            else if (!rxactive && in_packet) begin
                in_packet <= 1'b0;
            end

            // --- rate measurement ---
            // Timestamp each RXValid pulse while the packet is active and take
            // the elapsed time between consecutive pulses. The first RXValid of
            // a packet only arms the measurement.
            if (rxactive && rxvalid) begin
                if (have_prev_rxvalid && !rate_checked) begin
                    spacing_samples <= spacing_samples + 1;
                    if (($realtime - last_rxvalid_time) > byte_period_max) begin
                        byte_period_max <= $realtime - last_rxvalid_time;
                    end
                end
                have_prev_rxvalid <= 1'b1;
                last_rxvalid_time <= $realtime;
            end

            // --- PID capture and first-packet bookkeeping ---
            if (rxactive && rxvalid) begin
                bytes_this_packet <= bytes_this_packet + 1;
                if (!pid_captured) begin
                    pid          <= rxdata;
                    pid_captured <= 1'b1;
                end
                saw_any_packet <= 1'b1;

                // CHK_XCVR_FS. Evaluate once, on the first byte ever received.
                if (!xcvr_checked) begin
                    xcvr_checked <= 1'b1;
                    if (xcvrselect !== 1'b1 || termselect !== 1'b1) begin
                        uvm_report_error(MSG_ID,
                            $sformatf("CHK_XCVR_FS FAILED: on first received packet the DUT must select the FS transceiver and FS termination, but XcvrSelect=%0b TermSelect=%0b OpMode=%0b LineState=%0b. XcvrSelect=0/TermSelect=0 means the link negotiated High Speed.",
                                      xcvrselect, termselect, opmode, linestate));
                    end
                    else begin
                        uvm_report_info(MSG_ID,
                            $sformatf("CHK_XCVR_FS PASSED: XcvrSelect=1 TermSelect=1 (UTMI+ Full Speed) OpMode=%0b LineState=%0b",
                                      opmode, linestate),
                            UVM_LOW);
                    end
                end
            end

            // --- CHK_SOF_PERIOD ---
            if (sof_check_enabled && rxactive && rxvalid && !pid_captured
                && rxdata == USB_PID_SOF) begin
                if (have_last_sof && !sof_period_checked) begin
                    sof_period_checked <= 1'b1;
                    if (($realtime - last_sof_time) < SOF_PERIOD_FS_MIN ||
                        ($realtime - last_sof_time) > SOF_PERIOD_FS_MAX) begin
                        uvm_report_error(MSG_ID,
                            $sformatf("CHK_SOF_PERIOD FAILED: measured SOF interval %0t, expected a Full Speed frame interval between %0t and %0t. A 125 us interval indicates High Speed microframes.",
                                      ($realtime - last_sof_time),
                                      SOF_PERIOD_FS_MIN, SOF_PERIOD_FS_MAX));
                    end
                    else begin
                        uvm_report_info(MSG_ID,
                            $sformatf("CHK_SOF_PERIOD PASSED: SOF interval %0t is a Full Speed frame interval",
                                      ($realtime - last_sof_time)),
                            UVM_LOW);
                    end
                end
                last_sof_time <= $realtime;
                have_last_sof <= 1'b1;
            end
        end
    end

    // ---------------------------------------------------------------------
    // CHK_RATE_FS. Decide as soon as enough intervals have been collected, so
    // that the report lands well before final_phase counts severities.
    // ---------------------------------------------------------------------
    always_ff @(posedge utmi_clk) begin
        if (enabled && !rate_checked && spacing_samples >= RATE_SAMPLES_NEEDED) begin
            realtime measured_period;
            real     rate_mbit_s;

            rate_checked <= 1'b1;

            // Use the widest interval seen. See the CHK_RATE_FS note in the
            // file header: framing intervals are shorter than the steady-state
            // byte period, so the maximum is the unbiased estimator.
            measured_period = byte_period_max;

            // rate = 8 bits / byte_period, reported in Mbit/s. Scaling by 1us
            // rather than 1ns is what makes the unit Mbit/s: 8 bits per
            // 666.7 ns is 0.012 bit/ns, i.e. 12 bit/us, i.e. 12 Mbit/s. An
            // earlier revision divided by 1ns and therefore printed the rate in
            // Gbit/s, which rounded to "0.0 Mbit/s" in the log.
            rate_mbit_s = (measured_period == 0.0)
                        ? 0.0
                        : (8.0 * 1us) / measured_period;


            if (measured_period < FS_BYTE_PERIOD_MIN ||
                measured_period > FS_BYTE_PERIOD_MAX) begin
                uvm_report_error(MSG_ID,
                    $sformatf("CHK_RATE_FS FAILED: widest RXValid byte period %0t over %0d intervals, which is about %0.1f Mbit/s. Full Speed requires a byte period between %0t and %0t (12 Mbit/s). A byte period near 16.7 ns means High Speed (480 Mbit/s). Measured UTMI clock period %0t.",
                              measured_period, spacing_samples, rate_mbit_s,
                              FS_BYTE_PERIOD_MIN, FS_BYTE_PERIOD_MAX,
                              utmi_clk_period));
            end
            else begin
                uvm_report_info(MSG_ID,
                    $sformatf("CHK_RATE_FS PASSED: widest RXValid byte period %0t over %0d intervals, about %0.1f Mbit/s (Full Speed). Measured UTMI clock period %0t.",
                              measured_period, spacing_samples, rate_mbit_s,
                              utmi_clk_period),
                    UVM_LOW);
            end
        end
    end

    // ---------------------------------------------------------------------
    // CHK_SAW_TRAFFIC. Completeness and liveness guard.
    //
    // This must not use a fixed wall-clock deadline. Packet arrival time is a
    // property of firmware boot plus VIP link bring-up and is not known in
    // advance: in this test the first packet arrives around 308 us, so an
    // earlier revision that used a 300 us timeout reported a false
    // CHK_SAW_TRAFFIC failure 8 us before traffic legitimately started. Making
    // the timeout longer instead just reintroduces the opposite bug, where the
    // guard sits past the end of simulation and never runs at all, which lets
    // an unevaluated rate check masquerade as a pass.
    //
    // Instead the guard is driven by the stimulus itself. The sequence
    // triggers the OBS_WINDOW_EVENT uvm_event once its observation window has
    // closed, which is by definition the point at which all expected traffic
    // has either happened or not. Evaluating there is both reachable and
    // correctly ordered: it is still inside the run phase, so any
    // uvm_report_error is counted by final_phase and does flip the verdict.
    // ---------------------------------------------------------------------
    uvm_event obs_window_done;

    initial begin
        // Give the plusarg sampling initial block a chance to run first.
        #0;
        if (enabled) begin
            obs_window_done = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
            obs_window_done.wait_trigger();

            if (!saw_any_packet) begin
                uvm_report_error(MSG_ID,
                    "CHK_SAW_TRAFFIC FAILED: no USB packet was received on the UTMI interface during the entire observation window. The host never enumerated the device, so no speed measurement was possible. Check that the hub was enabled and connected (usb_hub_init_and_connect then usb_hub_connect) and that the device controller was enabled.");
            end
            else if (!rate_checked) begin
                uvm_report_error(MSG_ID,
                    $sformatf("CHK_RATE_FS FAILED: only %0d RXValid intervals were observed during the observation window, need %0d to measure the line rate. Traffic started but stalled before a rate measurement could complete, so Full Speed operation was never actually confirmed.",
                              spacing_samples, RATE_SAMPLES_NEEDED));
            end
            else begin
                uvm_report_info(MSG_ID,
                    "observation window closed with all enabled checks evaluated",
                    UVM_LOW);
            end
        end
    end

endmodule
