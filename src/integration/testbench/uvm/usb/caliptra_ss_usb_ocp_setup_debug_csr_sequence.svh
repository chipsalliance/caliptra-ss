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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_DEBUG_CSR_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_DEBUG_CSR_SEQUENCE_SVH

// Bus-visible diagnostic contract. Only completed, externally checked USB
// requests advance the baseline generation. No transient FSM is predicted.
class caliptra_ss_usb_ocp_setup_debug_csr_sequence
    extends caliptra_ss_usb_ocp_setup_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_debug_csr_sequence)
    protected virtual caliptra_ss_usb_supersession_csr_if csr;
    protected logic [31:0] debug_baseline, status_baseline;
    protected int accepted_baseline, owners_checked = 0;

    covergroup diagnostic_cg with function sample(bit observed_ocp, int pass);
        option.per_instance = 1;
        observed_owner: coverpoint observed_ocp;
        ro_access: coverpoint pass {
            bins stable_read = {0};
            bins write_ones = {1};
            bins write_zeroes = {2};
        }
        owner_access: cross observed_owner, ro_access;
    endgroup

    function new(string name = "caliptra_ss_usb_ocp_setup_debug_csr_sequence");
        super.new(name);
        diagnostic_cg = new();
    endfunction

    protected task ocp_setup_csr_do_access_and_check_response(
        input bit setup_debug,
        input bit write_access,
        input logic [31:0] write_data,
        output logic [31:0] read_data);
        logic [1:0] response;
        bit completed;
        completed = 0;
        fork : bounded_bus
            begin
                csr.ocp_supersession_do_csr_access(setup_debug, write_access, write_data, read_data, response);
                completed = 1;
            end
            #(TRANSFER_TIMEOUT);
        join_any
        disable bounded_bus;
        if (!completed || (response !== 2'b00))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Diagnostic AXI access timed out or returned non-OKAY")
    endtask

    protected task ocp_setup_csr_do_read_pair_and_check_response(
        output logic [31:0] debug_data,
        output logic [31:0] status_data);
        ocp_setup_csr_do_access_and_check_response(1, 0, '0, debug_data);
        ocp_setup_csr_do_access_and_check_response(0, 0, '0, status_data);
    endtask

    protected task ocp_setup_csr_do_request_and_check_owner(
        input bit request_ocp,
        input logic [3:0] firmware_id);
        svt_usb_transfer req;
        logic [31:0] debug_data, status_data, expected_debug, expected_status, ignored;
        logic [11:0] expected_generation;
        int observed_delta, errors_before;
        bit observed_owner;
        req = ocp_setup_configure_request(request_ocp, request_ocp ? "DEBUG_OCP" : "DEBUG_LEGACY");
        ocp_setup_arm_scenario(firmware_id);
        fork
            ocp_setup_do_request_and_check_result(req, 0, svt_usb_transfer::DATA_STAGE, "DEBUG_OWNER");
            begin
                if (!request_ocp) ocp_setup_check_and_release_legacy(0);
            end
        join
        if (request_ocp) transfers_issued++;
        ocp_setup_check_request(0, req, request_ocp, 1, 1);
        mixed_checker.ocp_supersession_check_window(1);
        if (!mixed_checker.last_window_valid)
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Cannot credit diagnostic request without valid boundary evidence")
        observed_owner = mixed_checker.evidence[0].ocp_supersession_check_is_ocp();
        observed_delta = mixed_checker.accepted_setups - accepted_baseline;
        expected_generation = debug_baseline[11:0] + 12'(observed_delta);
        expected_debug = {19'd0, observed_owner, expected_generation};
        // FIFO bits are compared only with the initial AXI baseline. These
        // reads cannot change FIFO contents; IDLE is checked only after STATUS.
        expected_status = {25'd0, 3'd0, status_baseline[3:0]};
        csr.enabled = 1;
        for (int pass = 0; pass < 3; pass++) begin
            errors_before = mixed_checker.errors;
            if (pass != 0) begin
                ocp_setup_csr_do_access_and_check_response(1, 1, pass == 1 ? 32'hFFFF_FFFF : 32'h0000_0000, ignored);
                ocp_setup_csr_do_access_and_check_response(0, 1, pass == 1 ? 32'hFFFF_FFFF : 32'h0000_0000, ignored);
            end
            // Repeat full-word reads to detect instability, reserved bits and
            // cross-register effects of writes to either RO address.
            repeat (2) begin
                ocp_setup_csr_do_read_pair_and_check_response(debug_data, status_data);
                if ((debug_data !== expected_debug) || (status_data !== expected_status))
                    mixed_checker.ocp_supersession_report_failure($sformatf(
                        "Diagnostic owner=%b pass=%0d debug=%08h/%08h status=%08h/%08h",
                        observed_owner, pass, debug_data, expected_debug,
                        status_data, expected_status));
            end
            if (errors_before == mixed_checker.errors)
                diagnostic_cg.sample(observed_owner, pass);
        end
        csr.enabled = 0;
        owners_checked++;
    endtask

    virtual task body();
        logic [31:0] debug_again, status_again;
        ocp_setup_do_initialize_and_check_capabilities();
        if (!uvm_config_db#(virtual caliptra_ss_usb_supersession_csr_if)::get(
            null, "uvm_test_top.env", "usb_supersession_csr_if", csr))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Existing AXI CSR interface is not configured")
        csr.ocp_supersession_check_csr_map();
        // Quiescent baseline precedes the first ARM. No diagnostic access is
        // issued while firmware is servicing latency-sensitive held work.
        csr.enabled = 1;
        ocp_setup_csr_do_read_pair_and_check_response(debug_baseline, status_baseline);
        ocp_setup_csr_do_read_pair_and_check_response(debug_again, status_again);
        csr.enabled = 0;
        if ($isunknown({debug_baseline, status_baseline}) ||
            (debug_again !== debug_baseline) || (status_again !== status_baseline) ||
            (debug_baseline[31:13] !== '0) ||
            (status_baseline[31:4] !== '0))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Initial diagnostic bus baseline is unknown, unstable, non-IDLE or has reserved bits set")
        accepted_baseline = mixed_checker.accepted_setups;
        ocp_setup_csr_do_request_and_check_owner(0, 0);
        ocp_setup_csr_do_request_and_check_owner(1, 1);
        if (owners_checked != 2)
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Missing observed legacy/OCP diagnostic checks")
        ocp_setup_publish_transfer_count();
    endtask
endclass
`endif
