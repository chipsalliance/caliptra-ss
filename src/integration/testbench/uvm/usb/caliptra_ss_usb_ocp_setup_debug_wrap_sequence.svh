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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_DEBUG_WRAP_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_DEBUG_WRAP_SEQUENCE_SVH

// CALIPTRA_SETUP_DEBUG's vendor contract, usb_ocp_recovery_reg.rdl:
// generation[11:0] increments modulo 4096 on each accepted Device0 EP0
// SETUP; owner[12] is atomic with generation and reserved[31:13] reads zero.
// This is not a USB/OCP-defined counter. USB 2.0 8.5.3/8.6.1 and OCP
// Recovery 1.1 8.5.1/9.2 define the independent request/service checks.
//
// Inherit only the existing AXI access helpers and SETUP base infrastructure.
// This body deliberately does not run the short diagnostic CSR campaign.
class caliptra_ss_usb_ocp_setup_debug_wrap_sequence
    extends caliptra_ss_usb_ocp_setup_debug_csr_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_debug_wrap_sequence)

    localparam int WRAP_REQUESTS = 4100;
    localparam int CHECKPOINT_INTERVAL = 256;
    localparam time INITIALIZATION_TIMEOUT = 100ms;
    protected int requests_checked = 0, owner_requests_checked[2];
    protected int legacy_requests_issued = 0;
    protected int checkpoints_issued = 0, diagnostic_words_checked = 0;
    protected int rollovers_checked = 0, wrap_windows_checked = 0;
    protected int sof_baseline;
    protected logic [3:0] wrap_progress = '0;
    protected logic [1:0] pre_wrap_owners = '0, post_wrap_owners = '0;
    protected logic [1:0] sampled_owners = '0;

    covergroup wrap_cg with function sample(bit observed_ocp,
        logic [11:0] observed_generation, bit complete_window);
        option.per_instance = 1;
        owner: coverpoint observed_ocp;
        generation_boundary: coverpoint observed_generation {
            bins penultimate = {12'hFFE};
            bins last = {12'hFFF};
            bins rollover = {12'h000};
            bins first_after = {12'h001};
            bins other = default;
        }
        before_wrap: coverpoint (observed_generation inside {12'hFFE, 12'hFFF})
            iff (observed_generation inside {12'hFFE, 12'hFFF, 12'h000, 12'h001});
        owner_side: cross owner, before_wrap;
        full_window: coverpoint complete_window iff (complete_window) {
            bins checked_ffe_fff_000_001 = {1};
        }
    endgroup

    function new(string name = "caliptra_ss_usb_ocp_setup_debug_wrap_sequence");
        super.new(name);
        wrap_cg = new();
        foreach (owner_requests_checked[i]) owner_requests_checked[i] = 0;
    endfunction

    protected task ocp_setup_wrap_check_diagnostics(
        input int ordinal, output bit matched);
        logic [31:0] debug_data, expected_debug;
        logic [11:0] expected_generation;
        logic observed_owner;
        expected_generation = debug_baseline[11:0] +
            12'(mixed_checker.accepted_setups - accepted_baseline);
        observed_owner = 1'bx;
        matched = 1;
        if (mixed_checker.last_accepted_setup == null) begin
            mixed_checker.ocp_supersession_report_failure(
                "Wrap diagnostic checkpoint has no independently accepted SETUP");
            matched = 0;
        end else begin
            observed_owner =
                mixed_checker.last_accepted_setup.ocp_supersession_check_is_ocp();
        end
        expected_debug = {19'd0, observed_owner, expected_generation};
        // All DATA/STATUS work has retired. No polling, firmware snapshots or
        // diagnostic traffic is inserted into the legacy response hot path.
        #1us;
        checkpoints_issued++;
        csr.enabled = 1;
        repeat (2) begin
            ocp_setup_csr_do_access_and_check_response(1, 0, '0, debug_data);
            if (debug_data !== expected_debug) begin
                mixed_checker.ocp_supersession_report_failure($sformatf(
                    "Wrap request=%0d accepted=%0d debug=%08h expected=%08h (generation/owner/reserved)",
                    ordinal, mixed_checker.accepted_setups - accepted_baseline,
                    debug_data, expected_debug));
                matched = 0;
            end else begin
                diagnostic_words_checked++;
            end
        end
        csr.enabled = 0;
        `uvm_info("SETUP_DEBUG_WRAP_CSR", $sformatf(
            "request=%0d accepted=%0d generation=%03h owner=%b matched=%b",
            ordinal, mixed_checker.accepted_setups - accepted_baseline,
            expected_generation, observed_owner, matched), UVM_NONE)
    endtask

    protected function void ocp_setup_wrap_credit_request(
        input logic [11:0] expected_generation, input bit observed_ocp,
        input bit valid_request);
        bit complete_window;
        complete_window = 0;
        if (!valid_request) begin
            // A later matching CSR value cannot repair missing wire evidence
            // or a failed checkpoint within the contiguous rollover window.
            wrap_progress = '0;
            return;
        end
        requests_checked++;
        owner_requests_checked[int'(observed_ocp)]++;
        case (expected_generation)
            12'hFFE: begin
                wrap_progress = 4'b0001;
                pre_wrap_owners = 2'b01 << int'(observed_ocp);
                post_wrap_owners = '0;
            end
            12'hFFF: begin
                if (wrap_progress === 4'b0001) begin
                    wrap_progress = 4'b0011;
                    pre_wrap_owners[int'(observed_ocp)] = 1;
                end else wrap_progress = '0;
            end
            12'h000: begin
                if (wrap_progress === 4'b0011) begin
                    wrap_progress = 4'b0111;
                    post_wrap_owners[int'(observed_ocp)] = 1;
                    rollovers_checked++;
                end else wrap_progress = '0;
            end
            12'h001: begin
                if (wrap_progress === 4'b0111) begin
                    post_wrap_owners[int'(observed_ocp)] = 1;
                    if ((pre_wrap_owners === 2'b11) &&
                        (post_wrap_owners === 2'b11)) begin
                        wrap_progress = 4'b1111;
                        complete_window = 1;
                        wrap_windows_checked++;
                        `uvm_info("SETUP_DEBUG_WRAP_COVERAGE",
                            "Checked contiguous FFE/FFF/000/001: both owners fully serviced on both sides",
                            UVM_NONE)
                    end else begin
                        mixed_checker.ocp_supersession_report_failure(
                            "Wrap boundary did not service both legacy/OCP owners on both sides");
                        wrap_progress = '0;
                    end
                end else wrap_progress = '0;
            end
            default: wrap_progress = '0;
        endcase
        wrap_cg.sample(observed_ocp, expected_generation, complete_window);
    endfunction

    virtual task body();
        svt_usb_transfer req;
        logic [31:0] debug_again;
        logic [11:0] scheduled_generation, observed_generation;
        int accepted_before, errors_before, windows_before, initial_arm_errors;
        bit request_ocp, observed_ocp, checkpoint, diagnostic_match, request_valid;

        // Reconfiguration can spawn persistent VIP protocol workers in the
        // caller's process tree. Keep initialization outside the scope being
        // cancelled, so only the watchdog is terminated after discovery.
        fork : initialization_watchdog
            begin
                #(INITIALIZATION_TIMEOUT);
                `uvm_fatal("SETUP_DEBUG_WRAP", "Normal USB/OCP discovery did not retire within 100 ms")
            end
        join_none
        ocp_setup_do_initialize_and_check_capabilities();
        disable initialization_watchdog;
        if (!uvm_config_db#(virtual caliptra_ss_usb_supersession_csr_if)::get(
            null, "uvm_test_top.env", "usb_supersession_csr_if", csr))
            `uvm_fatal("SETUP_DEBUG_WRAP", "Existing AXI CSR interface is not configured")
        csr.ocp_supersession_check_csr_map();
        mixed_checker.ocp_supersession_configure_acceptance_tracking(dev_addr_v);
        sof_baseline = mixed_checker.observed_sofs;
        accepted_baseline = mixed_checker.accepted_setups;
        windows_before = mixed_checker.windows;
        #1us;
        csr.enabled = 1;
        ocp_setup_csr_do_access_and_check_response(1, 0, '0, debug_baseline);
        ocp_setup_csr_do_access_and_check_response(1, 0, '0, debug_again);
        csr.enabled = 0;
        if ($isunknown(debug_baseline) || (debug_again !== debug_baseline) ||
            (debug_baseline[31:13] !== '0))
            `uvm_fatal("SETUP_DEBUG_WRAP",
                "Initial diagnostic baseline is unknown, unstable or has reserved bits set")
        if (mixed_checker.accepted_setups != accepted_baseline)
            `uvm_fatal("SETUP_DEBUG_WRAP", "Unexpected USB SETUP during diagnostic baseline")

        // First ARM ends normal discovery service. Subsequent claimed reads
        // need only a passive checker window, not a command or MCU snapshot.
        // Re-arm only for legacy requests, draining their old sticky IRQs.
        initial_arm_errors = mixed_checker.errors;
        ocp_setup_arm_scenario(11);
        for (int ordinal = 1; ordinal <= WRAP_REQUESTS; ordinal++) begin
            scheduled_generation = debug_baseline[11:0] + 12'(ordinal);
            // Baseline positions stimulus only. Payload expectations remain
            // runtime-discovered PROT_CAP and the image-owned descriptor.
            // FFE/FFF and 000/001 each exercise legacy then OCP service.
            request_ocp = !(scheduled_generation inside {12'hFFE, 12'h000});
            checkpoint = ((ordinal % CHECKPOINT_INTERVAL) == 0) ||
                (ordinal == WRAP_REQUESTS) ||
                (scheduled_generation inside {12'hFFE, 12'hFFF, 12'h000, 12'h001});
            accepted_before = mixed_checker.accepted_setups;
            errors_before = (ordinal == 1) ? initial_arm_errors : mixed_checker.errors;
            if (ordinal != 1) begin
                if (!request_ocp) ocp_setup_arm_scenario(11);
                else mixed_checker.ocp_supersession_configure_window(
                    scenario_generation, dev_addr_v);
            end
            req = ocp_setup_configure_request(request_ocp,
                $sformatf("WRAP_%0d_%s", ordinal, request_ocp ? "OCP" : "LEGACY"));
            if (!request_ocp) legacy_requests_issued++;
            fork
                ocp_setup_do_request_and_check_result(req, 0,
                    svt_usb_transfer::DATA_STAGE,
                    $sformatf("SETUP_DEBUG_WRAP_%0d", ordinal));
                begin
                    if (!request_ocp) ocp_setup_check_and_release_legacy(0);
                end
            join
            if (request_ocp) transfers_issued++;
            ocp_setup_check_request(0, req, request_ocp, 1, 1);
            // Progress is already published by ARM/RELEASE. Comparing these
            // retained counts adds no command/snapshot to claimed traffic.
            if (request_ocp) ocp_setup_check_service_counts();
            mixed_checker.ocp_supersession_check_window(1);
            observed_ocp = 0;
            if ((mixed_checker.accepted_setups != accepted_before + 1) ||
                (mixed_checker.accepted_setups - accepted_baseline != ordinal))
                mixed_checker.ocp_supersession_report_failure($sformatf(
                    "Wrap request=%0d accepted before/after/baseline=%0d/%0d/%0d; require exactly one new accepted SETUP",
                    ordinal, accepted_before, mixed_checker.accepted_setups, accepted_baseline));
            if (mixed_checker.evidence.size() == 1) begin
                observed_ocp = mixed_checker.evidence[0].ocp_supersession_check_is_ocp();
                if ((mixed_checker.last_accepted_setup != mixed_checker.evidence[0]) ||
                    (observed_ocp !== request_ocp))
                    mixed_checker.ocp_supersession_report_failure(
                        "Wrap accepted request identity/owner differs from the issued request");
            end
            diagnostic_match = 1;
            if (checkpoint) begin
                ocp_setup_wrap_check_diagnostics(ordinal, diagnostic_match);
                if (diagnostic_match) sampled_owners[int'(observed_ocp)] = 1;
            end
            // Catch unsolicited/retried SETUPs even during quiet AXI windows.
            if (mixed_checker.accepted_setups != accepted_before + 1)
                mixed_checker.ocp_supersession_report_failure(
                    "Accepted SETUP count changed during the quiet wrap checkpoint");
            observed_generation = debug_baseline[11:0] +
                12'(mixed_checker.accepted_setups - accepted_baseline);
            request_valid = mixed_checker.last_window_valid &&
                (mixed_checker.errors == errors_before) && diagnostic_match;
            ocp_setup_wrap_credit_request(observed_generation, observed_ocp, request_valid);
        end

        if ((mixed_checker.accepted_setups - accepted_baseline != WRAP_REQUESTS) ||
            (requests_checked != WRAP_REQUESTS) ||
            (mixed_checker.windows - windows_before != WRAP_REQUESTS) ||
            (owner_requests_checked[0] != legacy_requests_issued) ||
            (owner_requests_checked[1] != WRAP_REQUESTS - legacy_requests_issued) ||
            (sampled_owners !== 2'b11) ||
            (diagnostic_words_checked != 2 * checkpoints_issued) ||
            (rollovers_checked < 1) || (wrap_windows_checked < 1) ||
            (mixed_checker.observed_sofs <= sof_baseline))
            mixed_checker.ocp_supersession_report_failure(
                "Missing exact accepted count, checked service/diagnostics, both-owner rollover or live SOF coverage");
        `uvm_info("SETUP_DEBUG_WRAP_SUMMARY", $sformatf(
            "stimulus=%0d accepted=%0d checked=%0d legacy/OCP=%0d/%0d AXI-checkpoints=%0d matched-words=%0d rollovers=%0d full-windows=%0d SOFs=%0d baseline=%08h",
            WRAP_REQUESTS, mixed_checker.accepted_setups - accepted_baseline,
            requests_checked, owner_requests_checked[0], owner_requests_checked[1],
            checkpoints_issued, diagnostic_words_checked, rollovers_checked,
            wrap_windows_checked, mixed_checker.observed_sofs - sof_baseline,
            debug_baseline), UVM_NONE)
        ocp_setup_publish_transfer_count();
        // Completion is distinct from a passing verdict: all errors remain
        // visible, and the inherited test still owns STOP, halt and AXI drain.
        uvm_config_db#(bit)::set(
            null, "", "usb_setup_debug_wrap_stimulus_completed", 1);
    endtask
endclass
`endif
