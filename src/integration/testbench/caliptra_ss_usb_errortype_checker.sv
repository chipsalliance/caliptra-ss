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

`ifndef CALIPTRA_SS_USB_ERRORTYPE_CHECKER_SV
`define CALIPTRA_SS_USB_ERRORTYPE_CHECKER_SV

// =============================================================================
// Verdict for the PIE error report, pie_errortype.
//
// Watches the device PIE and FAILS the test if the error code the suite was
// written to produce is never reported.
//
// WHY THIS EXISTS
//
// The nine caliptra_ss_usb_hs_dev_err_* suites were written as pure stimulus
// with NO checker: nothing in those tests or their sequences ever referenced
// errortype outside a comment. TESTCASE PASSED therefore meant only "the
// sequence body ran and no VIP check fired" - it said nothing about whether
// pie_errortype ever took the intended value. The acceptance criterion was a
// MANUAL coverage-database inspection after the run, recorded in
// USB_TMP_ERR_INJECT_caliptra_ss_top_tb_regression.yml.
//
// That gap produced a false pass. caliptra_ss_usb_hs_dev_err_short_pkt was
// reported PASSED while a wave inspection showed pie_errortype never took the
// value 0x8 the suite exists to cover, and its firmware log recorded only one
// EP1 completion where the sequence drives two clean legs plus an injection.
// A test that cannot fail when its own stimulus does not arrive is not a test,
// so the verdict is moved into the testbench here.
//
// WHAT IT WATCHES, AND WHY THAT EXACT CONJUNCTION
//
// The qualification below is a deliberate copy of the coverpoint in
// src/usb/coverage/usb_dev_ep_cov.sv:
//
//     always_comb xfer_done_for_me = xfer_for_me && endtransfer;
//     cp_errortype: coverpoint xfer_errortype iff (xfer_done_for_me && xfer_error)
//
// so a hit recorded here and a closed cp_errortype bin cannot disagree. If this
// module passes, the target bin closed; if it fails, the bin is still open. The
// check is therefore a direct proxy for the coverage goal rather than a second,
// independently drifting opinion about it.
//
// The PIE is instantiated ONCE and time-multiplexed across hub, dev0 and dev1,
// so pie_errortype is only meaningful for whoever pie_dev_selected currently
// points at. This module is parameterised on MY_SEL exactly as usb_dev_ep_cov
// is, and ignores every report belonging to another function. That is the same
// reason a hub STALL does not close the device sent_stall bin, and why
// caliptra_ss_usb_hs_hub_class_req_stall cannot substitute for
// caliptra_ss_usb_hs_dev_err_stall.
//
// HOW A SUITE TURNS IT ON
//
// Three plusargs, all supplied from the suite's own yaml, in the same style as
// +usb_device_wakeup_check on caliptra_ss_usb_hs_dev_lpm_l1_dev_wakeup:
//
//   +usb_errortype_check=1          enable the checker
//   +usb_errortype_check_sel=<N>    which function to check (the pie_dev_selected
//                                   value, i.e. the MY_SEL encoding below) -
//                                   REQUIRED because the PIE is shared across
//                                   hub/dev0/dev1 (see below) and all nine
//                                   caliptra_ss_usb_hs_dev_err_* suites target
//                                   dev0 only. Without this a dev1 instance
//                                   would be enabled on a function the test
//                                   never touches and would always report "no
//                                   error of any kind" - a false failure, not a
//                                   real one.
//   +usb_expect_errortype=<code>    the pie_errortype code, in DECIMAL, that
//                                   this suite must cause at least once
//
// Example, for a suite targeting tr_eop (0x8) on dev0 (MY_SEL=1):
//
//   plusargs:
//     - '+UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_short_pkt_test'
//     - '+usb_errortype_check=1'
//     - '+usb_errortype_check_sel=1'
//     - '+usb_expect_errortype=8'
//
// The code is decimal because $value$plusargs %d is the reliable form; the
// legend below prints both representations so the log is unambiguous.
//
// The three knobs are a matched set. Enabling the checker without an expected
// code or without a selected function is a setup mistake, not a silent
// observe-only mode, so it is reported as a uvm_error rather than ignored -
// otherwise a yaml typo would reinstate exactly the cannot-fail situation this
// module exists to remove.
//
// Without +usb_errortype_check the module is completely inert, so adding it has
// no effect on any other test in the tree.
//
// WHAT A FAILURE MESSAGE TELLS YOU
//
// The failure distinguishes the two causes, because they need different fixes:
//
//   no error reported at all  - the stimulus never reached the PIE, or reached
//                               it and was ACCEPTED rather than rejected. Look
//                               at the injection itself.
//   other errors reported     - the stimulus reached the PIE but produced a
//                               different outcome. The message lists what was
//                               reported, with endpoint and direction, which
//                               usually identifies the mismatch immediately.
//
// WHEN THE VERDICT IS EVALUATED
//
// Not in a `final` block: SystemVerilog runs `final` after end-of-simulation
// teardown, strictly AFTER caliptra_ss_usb_base_test::final_phase has already
// counted UVM_ERRORs and printed "TESTCASE PASSED" / "TESTCASE FAILED". A
// uvm_error raised in `final` prints in the log but can never flip that
// verdict - this was caught by a run that showed both the UVM_ERROR and
// "TESTCASE PASSED" in the same log. The verdict here is instead gated on the
// uvm_event usb_errortype_obs_window_done, the same wait-trigger idiom every
// other checker in this file uses, so it runs while run_phase is still active
// and uvm_error still counts. That event is triggered once, from
// request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.svh, which is
// the one common tail every err-injection sequence already calls.
// =============================================================================

module caliptra_ss_usb_errortype_checker #(

    // Which compound function this instance accounts for. Compared against
    // pie_dev_selected using the same encoding as usb_dev_ep_cov, i.e. the
    // USB_SEL_* constants of usb_cov_pkg.
    parameter int unsigned MY_SEL = 0,
    // Message id prefix, so a dev0 and a dev1 instance are distinguishable.
    parameter string       NAME   = "USB_ERRTYPE_DEV0"
) (
    input logic        clk,
    input logic        rst_n,

    // Function multiplexing. Same net usb_cov_probe_caliptra_ss taps from
    // usb_ocp_recovery_post_sync_arb_1.pie_dev_selected_i.
    input logic [1:0]  pie_dev_selected,

    // The PIE transfer report, from usb_pie_1.
    input logic        pie_endtransfer,
    input logic        pie_error,
    input logic [3:0]  pie_errortype,
    input logic [3:0]  pie_epinfo_epnr,
    input logic        pie_epinfo_epdir
);

    import uvm_pkg::*;
`include "uvm_macros.svh"

    bit        enabled;
    bit        sel_matches;
    bit        have_expectation;
    int        expected_code;
    int        check_sel;

    localparam string OBS_WINDOW_EVENT = "usb_errortype_obs_window_done";
    uvm_event obs_window_done;


    // Observation state. seen[c] is set the first time code c is reported for
    // this function; seen_count[c] counts every report of it.
    bit        seen       [0:15];
    int        seen_count [0:15];
    int        total_reports;

    // Endpoint and direction of the FIRST report of each code, so a code that
    // arrives on an unexpected endpoint is visible in the summary.
    int        first_ep   [0:15];
    bit        first_dir  [0:15];

    // Legend. RTL-derived from the inlined SetError procedure of
    // usb_pie.m.vhdl - see docs/CaliptraSSUSBErrorInjection.md section 2.
    // Codes 0x7, 0xC, 0xD and 0xE have no live assignment site in this PIE and
    // were removed from the coverpoint rather than waived; they are named here
    // only so an unexpected appearance would be legible rather than blank.
    function automatic string errortype_name(int unsigned code);
        case (code)
            4'h0:    return "NO_ERROR";
            4'h1:    return "PID_ENCODING";
            4'h2:    return "PID_UNKNOWN";
            4'h3:    return "PACKET_UNEXPECTED";
            4'h4:    return "TOKEN_CRC";
            4'h5:    return "DATA_CRC";
            4'h6:    return "TIMEOUT";
            4'h7:    return "BABBLE (no live site)";
            4'h8:    return "TR_EOP";
            4'h9:    return "SENT_RECEIVED_NAK";
            4'hA:    return "SENT_STALL";
            4'hB:    return "OVERRUN";
            4'hC:    return "SENT_EMPTYPACK (no live site)";
            4'hD:    return "BITSTUFF (no live site)";
            4'hE:    return "SYNC (no live site)";
            4'hF:    return "DATA_IGNORED_WRONG_DATA01";
            default: return "UNKNOWN";
        endcase
    endfunction

    // Rendered once at the end, listing every code actually reported.
    function automatic string observed_summary();
        string s;
        s = "";
        for (int i = 0; i < 16; i++)
            if (seen[i])
                s = {s, $sformatf("\n    0x%0h (%0d) %-30s x%0d, first on EP%0d %s",
                                  i, i, errortype_name(i), seen_count[i],
                                  first_ep[i], first_dir[i] ? "IN" : "OUT")};
        if (s == "")
            s = "\n    (none)";
        return s;
    endfunction

    // seen, seen_count, total_reports, first_ep and first_dir are reset inside
    // the always_ff below (on !rst_n) rather than here: a variable written by
    // an always_ff cannot also be written by a separate initial/always
    // process (VCS ICPD). enabled, have_expectation and expected_code are
    // plusarg-derived and never touched by the always_ff, so they stay here.
    initial begin
        bit have_sel;

        enabled          = 1'b0;
        sel_matches      = 1'b0;
        have_expectation = 1'b0;
        expected_code    = -1;
        check_sel        = -1;

        obs_window_done = uvm_event_pool::get_global(OBS_WINDOW_EVENT);
        enabled = $test$plusargs("usb_errortype_check");

        if (enabled) begin
            have_sel = $value$plusargs("usb_errortype_check_sel=%d", check_sel);
            have_expectation =
                $value$plusargs("usb_expect_errortype=%d", expected_code);

            if (!have_sel)
                // Deliberately an error, for the same reason a missing expected
                // code is an error: a checker enabled on the wrong function (or
                // on no function at all) would report "no error of any kind"
                // regardless of whether the suite's stimulus succeeded, which is
                // a false failure rather than a real one.
                `uvm_error(NAME,
                    "+usb_errortype_check was given without +usb_errortype_check_sel=<N>. The PIE is shared across hub/dev0/dev1, so this checker must be told which function (pie_dev_selected value) the suite actually targets, or an instance watching the wrong function will always report no error.")
            else if (check_sel != MY_SEL)
                `uvm_info(NAME,
                    $sformatf("+usb_errortype_check_sel=%0d does not match this instance's MY_SEL=%0d, so this instance stays inert for this test.",
                              check_sel, MY_SEL),
                    UVM_LOW)
            else
                sel_matches = 1'b1;

            if (!have_expectation)
                // Deliberately an error. A checker that is enabled but has
                // nothing to check would silently restore the cannot-fail
                // situation this module exists to remove.
                `uvm_error(NAME,
                    "+usb_errortype_check was given without +usb_expect_errortype=<code>. The two are a matched pair and must both appear in the suite yaml; with no expected code there is nothing to verdict. Add the code, in decimal, that this suite must cause the PIE to report.")
            else if ((expected_code < 0) || (expected_code > 15)) begin
                `uvm_error(NAME,
                    $sformatf("+usb_expect_errortype=%0d is out of range; a pie_errortype code is 4 bits, so 0 to 15 decimal. Nothing can be verdicted against it.",
                              expected_code))
                have_expectation = 1'b0;
            end
            else if (sel_matches)
                `uvm_info(NAME,
                    $sformatf("enabled on function MY_SEL=%0d: this test must cause pie_errortype = 0x%0h (%0d, %s) to be reported at least once, qualified exactly as the cp_errortype coverpoint is (pie_dev_selected match, pie_endtransfer, pie_error).",
                              MY_SEL, expected_code, expected_code,
                              errortype_name(expected_code)),
                    UVM_LOW)
        end
    end


    // -------------------------------------------------------------------------
    // Sampling
    //
    // Same conjunction as the coverpoint: the report belongs to this function,
    // the transfer is ending, and the PIE flagged an error. Sampled on the
    // clock edge rather than combinationally so a transient on the way to
    // endtransfer cannot register a spurious code.
    // -------------------------------------------------------------------------
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            total_reports <= 0;
            for (int i = 0; i < 16; i++) begin
                seen[i]       <= 1'b0;
                seen_count[i] <= 0;
                first_ep[i]   <= -1;
                first_dir[i]  <= 1'b0;
            end
        end
        else if (enabled && sel_matches &&
            (pie_dev_selected == MY_SEL[1:0]) &&
            pie_endtransfer && pie_error) begin


            total_reports             <= total_reports + 1;
            seen_count[pie_errortype] <= seen_count[pie_errortype] + 1;

            if (!seen[pie_errortype]) begin
                seen[pie_errortype]      <= 1'b1;
                first_ep[pie_errortype]  <= int'(pie_epinfo_epnr);
                first_dir[pie_errortype] <= pie_epinfo_epdir;

                `uvm_info(NAME,
                    $sformatf("pie_errortype = 0x%0h (%0d, %s) reported for the first time, on EP%0d %s.",
                              pie_errortype, pie_errortype,
                              errortype_name(pie_errortype),
                              pie_epinfo_epnr,
                              pie_epinfo_epdir ? "IN" : "OUT"),
                    UVM_LOW)
            end
        end
    end


    // -------------------------------------------------------------------------
    // Verdict
    //
    // Gated on obs_window_done rather than a `final` block: `final` runs after
    // end-of-simulation teardown, strictly AFTER
    // caliptra_ss_usb_base_test::final_phase has already counted UVM_ERRORs and
    // printed TESTCASE PASSED/FAILED, so a uvm_error raised there can never
    // flip the verdict - only the log line. Waiting on the event instead means
    // this block runs while run_phase is still active, which is when
    // uvm_error actually counts. The event is triggered once by
    // request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.svh.
    // -------------------------------------------------------------------------
    initial begin
        // Let the plusarg-sampling initial block above run first so enabled,
        // sel_matches and have_expectation are resolved before this blocks.
        #0;
        if (enabled && sel_matches && have_expectation) begin
            obs_window_done.wait_trigger();

            if (seen[expected_code[3:0]])
                `uvm_info(NAME,
                    $sformatf("PASS: expected pie_errortype = 0x%0h (%0d, %s) was reported %0d time(s). The matching cp_errortype bin is closed.%s",
                              expected_code, expected_code,
                              errortype_name(expected_code),
                              seen_count[expected_code[3:0]],
                              observed_summary()),
                    UVM_LOW)
            else if (total_reports == 0)
                `uvm_error(NAME,
                    $sformatf("expected pie_errortype = 0x%0h (%0d, %s) but the PIE reported NO error of any kind on function MY_SEL=%0d. The injected stimulus did not produce a rejected transfer: either it never reached the PIE, or it reached it and was accepted. The target coverage bin is still open, so this test covered nothing.",
                              expected_code, expected_code,
                              errortype_name(expected_code), MY_SEL))
            else
                `uvm_error(NAME,
                    $sformatf("expected pie_errortype = 0x%0h (%0d, %s) but it was never reported. The PIE did report %0d other error(s), so the stimulus reached it but produced a different outcome than intended. Observed:%s",
                              expected_code, expected_code,
                              errortype_name(expected_code),
                              total_reports, observed_summary()))
        end
    end


endmodule

`endif // CALIPTRA_SS_USB_ERRORTYPE_CHECKER_SV

// File contains AI-generated response based on internal company sources
