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
// caliptra_ss_mcu_console_fail_checker
//
// Purpose
//   Make an MCU firmware failure message actually fail the test.
//
//   MCU test firmware reports problems by printing to the MCI DEBUG_OUT
//   console, for example
//
//     MCU: FAIL - enumeration timeout (got 0 of 3)
//
//   and then halting with csr_write_mpmc_halt(). Halting is exactly what a
//   successful test also does, and the console text is read by no checker, so
//   the UVM verdict in caliptra_ss_usb_base_test::final_phase saw zero
//   UVM_ERRORs and printed "* TESTCASE PASSED". A run in which the firmware
//   never received a single SETUP packet therefore came back green. This
//   module closes that gap: it reads the same character stream the console
//   monitor writes to mcu_console.log, and raises a UVM_ERROR for any line
//   containing "FAIL".
//
// What is observed
//   The MCI DEBUG_OUT character stream, taken from inside
//   caliptra_ss_top_tb_services where the console monitor already decodes it
//   (char_valid = mailbox_data_val & mailbox_write, char_data =
//   mailbox_data[7:0]). Characters are accumulated into a line buffer and the
//   completed line is matched on newline or carriage return, so the match is
//   done on whole console lines rather than on a sliding character window.
//
// What is checked
//   CHK_MCU_CONSOLE_FAIL   No console line printed by the MCU firmware may
//                          contain the substring "FAIL". Every offending line
//                          is reported, with its simulation time and full
//                          text, so a run that fails several phases still
//                          shows all of them instead of only the first.
//
// Verdict integration
//   Failures use uvm_report_error, not $error, for the same reason as
//   caliptra_ss_usb_suspend_resume_checker: only UVM report severities are
//   counted by caliptra_ss_usb_base_test::final_phase when it chooses between
//   TESTCASE PASSED and TESTCASE FAILED. A plain $error would print and leave
//   the verdict at PASSED, which is the bug this checker exists to close.
//
// Why substring "FAIL" and not an exact message
//   Firmware failure messages are free-form and differ per test, but the
//   convention across the test suites is a line containing FAIL (usually
//   "MCU: FAIL - <reason>"). Matching the substring needs no per-test table
//   and keeps working when a new failure message is added. The consequence is
//   that a benign console line containing the word FAIL would also fail the
//   test; that is intentional, because a firmware print carrying the word
//   FAIL should not be silently ignored.
//
// Enabling
//   Inert unless +mcu_console_fail_check is present on the simv command line,
//   so adding this module changes no existing test until that test opts in
//   through its .yml plusargs list. Use the "+mcu_console_fail_check=1" form
//   in the .yml: run_caliptra_test.py only forwards plusargs of the form
//   +NAME=VALUE, and $test$plusargs matches on prefix so the value is ignored.
// -------------------------------------------------------------------------

module caliptra_ss_mcu_console_fail_checker (
    input  logic       clk,
    input  logic       char_valid,
    input  logic [7:0] char_data
);

    import uvm_pkg::*;

    string MSG_ID = "MCU_CONSOLE_FAIL_CHK";

    // Substring that marks a firmware failure report.
    string FAIL_TOKEN = "FAIL";

    bit    enabled;

    // Accumulates the current console line. Flushed on LF or CR.
    string line_buf = "";

    int    fail_lines;

    initial begin
        enabled    = $test$plusargs("mcu_console_fail_check");
        fail_lines = 0;
        if (enabled) begin
            uvm_report_info(MSG_ID,
                "enabled: any MCU console line containing FAIL will be reported as a UVM_ERROR",
                UVM_LOW);
        end
    end

    // Plain substring search. SystemVerilog string methods have no find(), and
    // pulling in a regex/DPI dependency for this would be out of proportion.
    function automatic bit has_substr(string haystack, string needle);
        int hay_len;
        int ndl_len;
        hay_len = haystack.len();
        ndl_len = needle.len();
        if (ndl_len == 0 || ndl_len > hay_len) return 1'b0;
        for (int i = 0; i <= hay_len - ndl_len; i++) begin
            if (haystack.substr(i, i + ndl_len - 1) == needle) return 1'b1;
        end
        return 1'b0;
    endfunction

    // Sampled on negedge clk to match the console monitor in
    // caliptra_ss_top_tb_services, which decodes the same stream there.
    always @(negedge clk) begin
        if (enabled && char_valid) begin
            if (char_data inside {8'h0A, 8'h0D}) begin
                if (line_buf.len() > 0) begin
                    if (has_substr(line_buf, FAIL_TOKEN)) begin
                        fail_lines++;
                        uvm_report_error(MSG_ID,
                            $sformatf("CHK_MCU_CONSOLE_FAIL FAILED: MCU firmware reported a failure on its console at %0t: \"%s\". The firmware then halts, which is indistinguishable at pin level from a successful end of test, so without this check the run would have been reported as TESTCASE PASSED.",
                                      $time, line_buf));
                    end
                    line_buf = "";
                end
            end
            else begin
                line_buf = {line_buf, string'(char_data)};
            end
        end
    end

endmodule

// File contains AI-generated response based on internal company sources
