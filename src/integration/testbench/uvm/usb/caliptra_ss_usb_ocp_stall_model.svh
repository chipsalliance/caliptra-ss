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

`ifndef CALIPTRA_SS_USB_OCP_STALL_MODEL_SVH
`define CALIPTRA_SS_USB_OCP_STALL_MODEL_SVH

// Expected transitions are supplied by the stimulus/checker, never inferred
// from a DUT STALL or returned status code. USB 2.0 8.5.3.4 covers protocol
// STALL recovery at the next SETUP. OCP Recovery 1.1 8.5.1, 9.1 and 9.2
// define the error/status context. First-error-wins is a Caliptra-local
// contract, not a normative USB or OCP precedence rule.
class caliptra_ss_usb_ocp_stall_model extends uvm_object;
    `uvm_object_utils(caliptra_ss_usb_ocp_stall_model)

    protected bit stalled;
    protected ocp_protocol_error_e expected_code;
    protected int unsigned errors_noted;
    protected int unsigned accepted_setups;
    protected int unsigned status_reads;
    protected int unsigned status_mismatches;
    protected int unsigned stall_checks;

    function new(string name = "caliptra_ss_usb_ocp_stall_model");
        super.new(name);
        reset();
    endfunction

    function void reset();
        stalled = 1'b0;
        expected_code = OCP_PROTOCOL_ERROR_NONE;
        errors_noted = 0;
        accepted_setups = 0;
        status_reads = 0;
        status_mismatches = 0;
        stall_checks = 0;
    endfunction

    function void note_error(input ocp_protocol_error_e code);
        if (code === OCP_PROTOCOL_ERROR_NONE) return;
        errors_noted++;
        stalled = 1'b1;
        if (expected_code === OCP_PROTOCOL_ERROR_NONE) expected_code = code;
    endfunction

    // Call on an independently expected/validated accepted SETUP, not merely
    // because a status response or a STALL was observed.
    function void note_accepted_setup();
        accepted_setups++;
        stalled = 1'b0;
    endfunction

    function bit is_stalled();
        return stalled;
    endfunction

    function ocp_protocol_error_e expected_status_code();
        return expected_code;
    endfunction

    // Side-effect-free predicates support deterministic mutation selftests.
    function bit status_code_matches(input bit [7:0] actual);
        return actual === expected_code;
    endfunction

    // A completed DEVICE_STATUS read consumes the expected sticky code even
    // on mismatch. Never seed the next expectation from the returned value.
    // Reading status alone does not alter protocol-STALL state.
    function bit check_status_code(
        input bit [7:0] actual,
        input string label);

        bit valid;
        valid = status_code_matches(actual);
        status_reads++;
        if (!valid) begin
            status_mismatches++;
            `uvm_error("OCP_STALL_MODEL",
                $sformatf("%s: protocol error actual=0x%02h expected=0x%02h",
                          label, actual, expected_code))
        end
        expected_code = OCP_PROTOCOL_ERROR_NONE;
        return valid;
    endfunction

    function bit require_stalled(input string label);
        stall_checks++;
        if (!stalled)
            `uvm_error("OCP_STALL_MODEL",
                $sformatf("%s: expected model to be protocol-stalled", label))
        return stalled;
    endfunction

    function void report(input string label = "");
        `uvm_info("OCP_STALL_MODEL",
            $sformatf("%s: events=%0d setups=%0d reads=%0d mismatches=%0d stall_checks=%0d stalled=%0b code=0x%02h",
                      label, errors_noted, accepted_setups, status_reads,
                      status_mismatches, stall_checks, stalled, expected_code),
            UVM_LOW)
    endfunction
endclass

`endif // CALIPTRA_SS_USB_OCP_STALL_MODEL_SVH
