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

// Bus-visible diagnostic contract. Every observed accepted SETUP advances the
// generation, including interrupted requests and shared-helper traffic.
// Host-retained windows permit AXI sampling; local coverage owns transients.
class caliptra_ss_usb_ocp_setup_debug_csr_sequence
    extends caliptra_ss_usb_ocp_setup_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_debug_csr_sequence)
    protected virtual caliptra_ss_usb_supersession_csr_if csr;
    protected logic [31:0] debug_baseline, status_baseline;
    protected int accepted_baseline, owners_checked = 0;
    protected logic [3:0] states_checked = '0;
    protected logic [2:0] fifo_checked = '0;
    // CALIPTRA_STATUS's documented encodings, not DUT FSM enum values.
    localparam logic [2:0] CSR_IDLE = 0, CSR_DATA = 3,
                           CSR_STATUS = 4, CSR_STALL = 5;
    localparam int FIFO_UNMEASURED = 0, FIFO_EMPTY = 1,
                   FIFO_PARTIAL = 2, FIFO_FULL = 3;

    covergroup diagnostic_cg with function sample(bit observed_ocp,
        logic [2:0] state, int occupancy, int pass);
        option.per_instance = 1;
        observed_owner: coverpoint observed_ocp;
        ro_access: coverpoint pass {
            bins stable_read = {0};
            bins write_ones = {1};
            bins write_zeroes = {2};
        }
        retained_state: coverpoint state {
            bins idle = {CSR_IDLE};
            bins data_pending = {CSR_DATA};
            bins status_pending = {CSR_STATUS};
            bins stalled = {CSR_STALL};
        }
        fifo_occupancy: coverpoint occupancy iff (occupancy != FIFO_UNMEASURED) {
            bins empty = {FIFO_EMPTY};
            bins partial = {FIFO_PARTIAL};
            bins full = {FIFO_FULL};
        }
        owner_access: cross observed_owner, ro_access;
        state_access: cross retained_state, ro_access;
        fifo_access: cross fifo_occupancy, ro_access;
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

    protected task ocp_setup_csr_do_check_retained_window(
        input logic [2:0] state,
        input logic [3:0] fifo_bits,
        input int occupancy = FIFO_UNMEASURED);
        logic [31:0] debug_data, status_data, expected_debug, expected_status, ignored;
        logic [11:0] expected_generation;
        int observed_delta, errors_before, window_errors_before;
        bit observed_owner;
        if (mixed_checker.last_accepted_setup == null)
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "No independently observed accepted SETUP")
        observed_owner = mixed_checker.last_accepted_setup.ocp_supersession_check_is_ocp();
        observed_delta = mixed_checker.accepted_setups - accepted_baseline;
        expected_generation = debug_baseline[11:0] + 12'(observed_delta);
        expected_debug = {19'd0, observed_owner, expected_generation};
        expected_status = {25'd0, state, fifo_bits};
        // The host has stopped issuing tokens, and the fixture never consumes
        // FIFO contents without an explicit command. This is not a request
        // servicing delay and does not stretch the legacy firmware hot path.
        #1us;
        csr.enabled = 1;
        window_errors_before = mixed_checker.errors;
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
                        "Diagnostic owner=%b state=%0d fifo=%0d pass=%0d debug=%08h/%08h status=%08h/%08h",
                        observed_owner, state, occupancy, pass, debug_data, expected_debug,
                        status_data, expected_status));
            end
            if (errors_before == mixed_checker.errors) begin
                diagnostic_cg.sample(observed_owner, state, occupancy, pass);
                if ((pass == 2) && (window_errors_before == mixed_checker.errors)) begin
                    case (state)
                        CSR_IDLE: states_checked[0] = 1;
                        CSR_DATA: states_checked[1] = 1;
                        CSR_STATUS: states_checked[2] = 1;
                        CSR_STALL: states_checked[3] = 1;
                        default: `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Unsupported retained window")
                    endcase
                    if (occupancy != FIFO_UNMEASURED)
                        fifo_checked[occupancy - FIFO_EMPTY] = 1;
                end
            end
        end
        csr.enabled = 0;
    endtask

    protected task ocp_setup_csr_do_request_and_check_owner(
        input bit request_ocp,
        input logic [3:0] firmware_id);
        svt_usb_transfer req;
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
        ocp_setup_csr_do_check_retained_window(CSR_IDLE, status_baseline[3:0]);
        owners_checked++;
    endtask

    protected task ocp_setup_csr_do_pending_and_check_state(input bit data_completed);
        svt_usb_transfer req;
        svt_usb_transfer::xfer_stage_enum boundary;
        boundary = data_completed ? svt_usb_transfer::DATA_STAGE :
                                    svt_usb_transfer::SETUP_STAGE;
        req = ocp_setup_configure_request(1, "DEBUG_RETAINED_READ");
        ocp_setup_arm_scenario(11);
        ocp_setup_do_request_and_check_result(req, 1, boundary, "DEBUG_RETAINED_READ");
        transfers_issued++;
        ocp_setup_check_request(0, req, 1, 0, data_completed);
        mixed_checker.ocp_supersession_check_window(1);
        if (!mixed_checker.last_window_valid)
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Retained request lacks its completed packet boundary")
        ocp_setup_csr_do_check_retained_window(
            data_completed ? CSR_STATUS : CSR_DATA, status_baseline[3:0]);
        // A real subsequent SETUP, not an internal state write, resumes USB.
        ocp_setup_csr_do_request_and_check_owner(1, 11);
    endtask

    protected task ocp_setup_csr_do_stall_and_check_state();
        svt_usb_transfer req;
        logic [7:0] empty[$];
        bit [7:0] status[$];
        // OCP 9.1: unsupported command sets the protocol error. The local
        // persistent-STALL diagnostic contract is checked only after the VIP
        // independently observes the actual STALL handshake.
        req = ocp_setup_configure_request(1, "DEBUG_STALL",
                                          ocp_cmd_t'(OCP_CMD_MIN - 1));
        ocp_setup_arm_scenario(11);
        ocp_setup_do_request_and_check_result(req, 0, svt_usb_transfer::DATA_STAGE,
                                            "DEBUG_STALL", .expect_stall(1));
        transfers_issued++;
        mixed_checker.ocp_supersession_check_request(0, req, 0, 0, empty,
                                                     TRANSFER_TIMEOUT, .expect_stall(1));
        mixed_checker.ocp_supersession_check_window(1);
        if (!mixed_checker.last_window_valid)
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "No observed STALL for diagnostic window")
        ocp_setup_csr_do_check_retained_window(CSR_STALL, status_baseline[3:0]);
        ocp_setup_csr_do_request_and_check_owner(1, 11);
        ocp_do_read_and_check_device_status(status, "DEBUG_STALL_ERROR");
        if ((status.size() <= OCP_OFF_DS_PROT_ERROR) ||
            (status[OCP_OFF_DS_PROT_ERROR] !== OCP_PROTOCOL_ERROR_UNSUPPORTED_COMMAND))
            `uvm_error("SUPERSESSION_DEBUG_CSR", "Unsupported command did not retain its OCP error")
        ocp_do_read_and_check_device_status(status, "DEBUG_STALL_ERROR_CLEAR");
        if ((status.size() <= OCP_OFF_DS_PROT_ERROR) ||
            (status[OCP_OFF_DS_PROT_ERROR] !== OCP_PROTOCOL_ERROR_NONE))
            `uvm_error("SUPERSESSION_DEBUG_CSR", "OCP error did not clear on the agent read")
    endtask

    protected virtual function void ocp_configure_xfer(input svt_usb_transfer request);
        super.ocp_configure_xfer(request);
        if ((request.setup_data_w_value[7:0] == OCP_CMD_INDIRECT_FIFO_DATA) &&
            (request.setup_data_bmrequesttype_dir == svt_usb_types::HOST_TO_DEVICE)) begin
            // Same control-OUT configuration as the existing FIFO consumers:
            // USB 2.0 9.3.5 sends exactly wLength bytes, no bulk-style ZLP.
            usb_cfg.remote_device_cfg[0].endpoint_cfg[0].
                allow_aligned_transfer_without_zero_length = 1;
            request.aligned_transfer_ends_with_zero_length = 0;
        end
    endfunction

    protected task ocp_setup_csr_do_fifo_sample_and_check_unchanged(
        input fifo_status_s before_status, input int occupancy,
        input logic [3:0] fifo_bits);
        fifo_status_s after_status;
        bit [7:0] response[$];
        ocp_setup_csr_do_check_retained_window(CSR_IDLE, fifo_bits, occupancy);
        ocp_do_read_and_check_fifo_status(response, after_status, "DEBUG_FIFO_AFTER_RO");
        if (after_status !== before_status)
            `uvm_error("SUPERSESSION_DEBUG_CSR", "Diagnostic RO accesses changed FIFO flags, indices or capabilities")
    endtask

    protected task ocp_setup_csr_do_fifo_windows_and_check_status();
        fifo_status_s status, initial_status;
        bit [7:0] response[$], image[$], payload[$];
        bit [31:0] pattern[$];
        logic [15:0] caps;
        int unsigned chunk_limit, offset, chunk;
        caliptra_ss_usb_ocp_xfer_result_e result;
        bit saved_aligned;
        caps = {ocp_bytes[OCP_OFF_PC_AGENT_CAPS_HI], ocp_bytes[OCP_OFF_PC_AGENT_CAPS_LO]};
        if (!caps[OCP_CAP_INDIRECT_FIFO] || (ocp_bytes[OCP_OFF_PC_CMS_COUNT] == 0))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Runtime capabilities do not permit FIFO diagnostic coverage")
        saved_aligned = usb_cfg.remote_device_cfg[0].endpoint_cfg[0].
                            allow_aligned_transfer_without_zero_length;
        // CMS0 is the first of the runtime-advertised component spaces.
        ocp_do_recovery_ctrl_write(0, 0, 0, "DEBUG_FIFO_RECOVERY_CTRL");
        ocp_do_read_and_check_fifo_status(response, initial_status, "DEBUG_FIFO_CAPABILITIES");
        chunk_limit = ocp_get_max_chunk_dwords(initial_status);
        // A bounded diagnostic fixture budget, not an assumed hardware depth.
        if ((initial_status.fifo_size < 2) || (initial_status.fifo_size > 4096) ||
            (chunk_limit == 0) || (initial_status.region_type !== OCP_REGION_RECOVERY_CODE_WO))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Discovered FIFO exceeds diagnostic fixture limits or is not write-only code space")
        ocp_do_fifo_ctrl_write(0, 1, initial_status.fifo_size, "DEBUG_FIFO_RESET");
        ocp_do_read_and_check_fifo_status(response, status, "DEBUG_FIFO_EMPTY");
        if (!status.empty || status.full || (status.write_index !== status.read_index))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "FIFO reset did not establish the empty window")
        if ((status.fifo_size !== initial_status.fifo_size) ||
            (status.max_transfer_dwords !== initial_status.max_transfer_dwords) ||
            (status.region_type !== initial_status.region_type))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "FIFO capabilities changed across reset")
        initial_status = status;
        ocp_setup_csr_do_fifo_sample_and_check_unchanged(status, FIFO_EMPTY, 4'b0001);

        for (int unsigned i = 0; i < initial_status.fifo_size; i++)
            pattern.push_back(32'h5354_0000 | i);
        ocp_prepare_le_dword_image(pattern, image);
        // Keep the first complete batch small to retain a nonempty/nonfull
        // window. No fixture consumer runs until the explicit drain command.
        offset = 0;
        while (offset < initial_status.fifo_size) begin
            chunk = (offset == 0) ? 1 : initial_status.fifo_size - offset;
            if (chunk > chunk_limit) chunk = chunk_limit;
            ocp_prepare_image_payload_slice(image, offset, chunk, payload);
            ocp_do_fifo_data_write(payload, result, "DEBUG_FIFO_FILL");
            if (result != OCP_XFER_SUCCESS)
                `uvm_fatal("SUPERSESSION_DEBUG_CSR", "FIFO diagnostic fill did not complete")
            offset += chunk;
            ocp_do_read_and_check_fifo_status(response, status, "DEBUG_FIFO_FILL_STATUS");
            if ((status.read_index !== initial_status.read_index) ||
                status.empty || (status.write_index !==
                    ((initial_status.write_index + offset) % initial_status.fifo_size)))
                `uvm_fatal("SUPERSESSION_DEBUG_CSR", "FIFO changed without the commanded producer/consumer activity")
            if (offset == 1) begin
                if (status.full)
                    `uvm_fatal("SUPERSESSION_DEBUG_CSR", "No partial FIFO diagnostic window")
                ocp_setup_csr_do_fifo_sample_and_check_unchanged(status, FIFO_PARTIAL, 4'b0001);
            end
        end
        // Reuse the existing FIFO-ring fixture's full-capacity diagnostic
        // boundary. This is not a new ring-capacity compliance claim.
        if (!status.full || status.empty)
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "No stable full FIFO diagnostic window")
        ocp_setup_csr_do_fifo_sample_and_check_unchanged(status, FIFO_FULL, 4'b0101);
        ocp_setup_issue_mcu_command(CMD_FIFO_DRAIN);
        ocp_do_read_and_check_fifo_status(response, status, "DEBUG_FIFO_DRAINED");
        if (!status.empty || status.full || (status.write_index !== status.read_index))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Exact verified MCU drain did not establish empty FIFO")
        ocp_setup_csr_do_fifo_sample_and_check_unchanged(status, FIFO_EMPTY, 4'b0101);
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].
            allow_aligned_transfer_without_zero_length = saved_aligned;
    endtask

    virtual task body();
        logic [31:0] debug_again, status_again;
        ocp_setup_do_initialize_and_check_capabilities();
        if (!uvm_config_db#(virtual caliptra_ss_usb_supersession_csr_if)::get(
            null, "uvm_test_top.env", "usb_supersession_csr_if", csr))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Existing AXI CSR interface is not configured")
        csr.ocp_supersession_check_csr_map();
        mixed_checker.ocp_supersession_configure_acceptance_tracking(dev_addr_v);
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
        ocp_setup_csr_do_pending_and_check_state(0);
        ocp_setup_csr_do_pending_and_check_state(1);
        ocp_setup_csr_do_stall_and_check_state();
        ocp_setup_csr_do_fifo_windows_and_check_status();
        if ((states_checked !== 4'hF) || (fifo_checked !== 3'b111))
            `uvm_error("SUPERSESSION_DEBUG_CSR", "Missing checked retained-state/FIFO diagnostic coverage")
        ocp_setup_publish_transfer_count();
    endtask
endclass
`endif
