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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_ADDRESS_HANDOFF_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_ADDRESS_HANDOFF_SEQUENCE_SVH

// Reuse the ordinary project link/PHY profile and SOF service, not the
// termination testcase's reset-duration profile. The parent owns every
// enumeration request and checks its actual packets before advancing state.
class caliptra_ss_usb_ocp_setup_address_link_sequence
    extends caliptra_ss_usb_init_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_address_link_sequence)

    function new(string name = "caliptra_ss_usb_ocp_setup_address_link_sequence");
        super.new(name);
    endfunction

    virtual task body();
        resolve_xfer_handles(host_agent_h, usb_cfg, shared_status);
        wait_link_enabled();
        start_sof();
        #20us;
    endtask
endclass

// USB 2.0 9.1.1.4/9.1.1.5, 9.4.6/9.4.7, 5.5.5, 8.6.1:
//   Configured(1) -> configuration 0 -> completed SET_ADDRESS(2)
//   Configured(2) -> configuration 0 -> interrupted SET_ADDRESS(3).
// Cross each transition with old STATUS absent/completed, next SETUP at the
// retained/new address, DATA1 restart, and Configured-only L/O/L/O service.
// No Address-state OCP service or Configured-state SET_ADDRESS is an oracle.
class caliptra_ss_usb_ocp_setup_address_handoff_sequence
    extends caliptra_ss_usb_ocp_setup_debug_csr_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_setup_address_handoff_sequence)

    localparam time REQUEST_BOUND = 100us;
    localparam time ADDRESS_RECOVERY = 2ms; // USB 2.0 9.2.6.3, unscaled.
    protected caliptra_ss_usb_stale_publication_protocol gate;
    protected logic [15:0] wire_generation;
    protected logic [7:0] runtime_configuration;
    protected int runtime_interface = -1;
    protected logic [7:0] descriptor_bytes[$];
    protected logic [7:0] configuration_state;
    protected bit snapshots_available;
    protected int checked_requests, checked_windows, firmware_checks, claim_checks;
    protected int state_checks, completed_changes, interrupted_changes, service_groups;
    protected int status_armed_checks;
    protected int sof_baseline;

    function new(string name = "caliptra_ss_usb_ocp_setup_address_handoff_sequence");
        super.new(name);
        wire_generation = '0;
        snapshots_available = 0;
        checked_requests = 0;
        checked_windows = 0;
        firmware_checks = 0;
        claim_checks = 0;
        state_checks = 0;
        completed_changes = 0;
        interrupted_changes = 0;
        service_groups = 0;
        status_armed_checks = 0;
    endfunction

    protected function void require(input bit condition, input string message);
        if (!condition) begin
            `uvm_error("SETUP_ADDRESS_CHECK", message)
            `uvm_fatal("SETUP_ADDRESS_CHECK", "No credit or alternate-address repair after failed proof")
        end
    endfunction

    protected virtual function int ocp_get_iface_num();
        return runtime_interface;
    endfunction

    protected task command(input logic [3:0] opcode, input logic [3:0] argument = 0);
        bit acknowledged;
        require(command_generation !== 16'hFFFF, "MCU command generation exhausted");
        command_generation++;
        observer_vif.issue_mcu_command_bounded(
            opcode, command_generation, argument, REQUEST_BOUND, acknowledged);
        require(acknowledged, "Generation-qualified MCU command did not acknowledge");
    endtask

    protected task snapshot(output logic [31:0] dispatches,
                            output logic [31:0] configuration);
        bit found;
        command(observer_vif.MCU_COMMAND_PUBLISH_BASELINE);
        observer_vif.receive_snapshot(observer_vif.SNAPSHOT_STATE_BASELINE,
                                      command_generation, REQUEST_BOUND, found);
        require(found, "Generation-qualified 18-field MCU snapshot missing");
        require(observer_vif.snapshot_valid &&
                (observer_vif.snapshot_generation === command_generation) &&
                (observer_vif.snapshot_state === observer_vif.SNAPSHOT_STATE_BASELINE),
                "MCU snapshot was not bound to the acknowledged command generation");
        dispatches = observer_vif.get_snapshot_field(16);
        configuration = observer_vif.get_snapshot_field(10);
        require(!$isunknown({dispatches, configuration}), "Unknown MCU state/dispatch snapshot");
        require(observer_vif.get_snapshot_field(17) === 32'd2, "Unexpected shared fixture snapshot ABI");
        // DEVCMDSTAT[6:0] is deliberately NOT an expected address source.
    endtask

    protected function svt_usb_transfer request(
        input bit read_request, input logic [7:0] brequest,
        input logic [15:0] value, input int unsigned length,
        input string label, input bit ocp = 0);
        svt_usb_transfer req;
        logic [63:0] intended_setup;
        logic [7:0] intended_bmrequesttype;
        int unsigned intended_address;
        intended_bmrequesttype = (read_request ? 8'h80 : 8'h00) |
                                (ocp ? 8'h21 : 8'h00);
        intended_setup = {16'(length), (ocp ? 16'(runtime_interface) : 16'd0),
                          value, brequest, intended_bmrequesttype};
        intended_address = dev_addr_v;
        req = svt_usb_transfer::type_id::create(label);
        req.cfg = usb_cfg;
        req.fix_anchors(0, 0, 0);
        require(length <= 64, "Address checker supports only bounded single-packet responses");
        require(!ocp || ((runtime_interface >= 0) && (configuration_state !== 8'd0)),
                "OCP requires a runtime-discovered interface and completed configuration");
        // Inline constraints search the randomized object first; brequest is
        // also a public VIP member. Bind every external RHS explicitly.
        if (!req.randomize() with {
            xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
            device_address == local::dev_addr_v;
            endpoint_number == 0;
            setup_data_bmrequesttype_dir == (local::read_request ?
                svt_usb_types::DEVICE_TO_HOST : svt_usb_types::HOST_TO_DEVICE);
            setup_data_bmrequesttype_type == (local::ocp ? svt_usb_types::CLASS : svt_usb_types::STANDARD);
            setup_data_bmrequesttype_recipient == (local::ocp ?
                svt_usb_types::BMREQ_INTERFACE : svt_usb_types::BMREQ_DEVICE);
            setup_data_brequest == local::brequest;
            setup_data_w_value == local::value;
            setup_data_w_index == (local::ocp ? 16'(local::runtime_interface) : 16'd0);
            setup_data_w_length == 16'(local::length);
            payload_start_ix == 0;
            payload_intended_byte_count == local::length;
        }) begin
            `uvm_error("SETUP_ADDRESS_CHECK", "Required USB request randomization failed")
            `uvm_fatal("SETUP_ADDRESS_CHECK", label)
        end
        require((req.xfer_type === svt_usb_transfer::CONTROL_TRANSFER) &&
                (req.device_address === intended_address) && (req.endpoint_number === 0) &&
                (mixed_checker.ocp_supersession_get_setup_line(req) === intended_setup),
                $sformatf("%s constructed SETUP=%016h address=%0d EP=%0d; intended SETUP=%016h address=%0d EP0",
                    label, mixed_checker.ocp_supersession_get_setup_line(req),
                    req.device_address, req.endpoint_number, intended_setup, intended_address));
        return req;
    endfunction

    protected task open_window();
        require(wire_generation !== 16'hFFFF, "Wire generation exhausted");
        wire_generation++;
        mixed_checker.ocp_supersession_configure_window(wire_generation, 7'(dev_addr_v));
    endtask

    protected task submit(input svt_usb_transfer req);
        // Cancel only the watchdog, never a request/reconfigure process tree.
        fork : request_watchdog
            begin
                #(REQUEST_BOUND);
                `uvm_error("SETUP_ADDRESS_TIMEOUT", "Submitted USB transfer failed to retire within 100 us")
                `uvm_fatal("SETUP_ADDRESS_TIMEOUT", "No abort-as-success or retry repair")
            end
        join_none
        start_item(req, -1, p_sequencer.xfer_sequencer);
        finish_item(req, -1);
        req.end_event.wait_on();
        disable request_watchdog;
    endtask

    protected function void check_native(input svt_usb_transfer req,
        input bit complete, input int observed_length);
        `uvm_info("SETUP_ADDRESS_NATIVE", $sformatf(
            "request=%s submitted-address=%0d status=%s raw-results=%032h complete=%b observed-bytes=%0d",
            req.get_name(), req.device_address, req.status.name(), req.results_status,
            complete, observed_length), UVM_NONE)
        // VIP bit 5 reports a zero-length packet. Every completed control
        // request here independently requires a STATUS ZLP on the wire.
        // Use the shared native-success definition; never mask error bits.
        if (complete)
            require(caliptra_ss_usb_xfer_successful(req),
                    "Native result has errors/abort (only ACCEPT with raw 0 or 0x20 is legal)");
        else
            require((req.status === svt_sequence_item::ABORTED) &&
                    (req.results_status === 128'd0),
                    "Pre-token interrupted submission did not retire explicitly ABORTED/clean");
    endfunction

    protected task close_window(input int expected_setups);
        mixed_checker.ocp_supersession_check_window(expected_setups);
        require(mixed_checker.last_window_valid, "Address evidence window failed exact occurrence inventory");
        checked_windows++;
    endtask

    protected task claim_proof();
        logic [31:0] debug_word, expected;
        expected = {19'd0, 1'b1, 12'(mixed_checker.accepted_setups)};
        csr.enabled = 1;
        repeat (2) begin
            ocp_setup_csr_do_access_and_check_response(1, 0, '0, debug_word);
            require(debug_word === expected, "OCP class service lacked accepted-generation/owner claim evidence");
        end
        csr.enabled = 0;
        claim_checks++;
        `uvm_info("SETUP_ADDRESS_CLAIM", $sformatf(
            "accepted=%0d debug=%08h expected=%08h two AXI reads matched",
            mixed_checker.accepted_setups, debug_word, expected), UVM_NONE)
    endtask

    protected task run_request(input svt_usb_transfer req,
        input logic [7:0] expected[$], output logic [7:0] response[$],
        input bit discovery = 0);
        logic [31:0] before_dispatch, after_dispatch, fw_configuration;
        bit ocp;
        ocp = (req.setup_data_bmrequesttype_type === svt_usb_types::CLASS);
        response.delete();
        if (snapshots_available) snapshot(before_dispatch, fw_configuration);
        open_window();
        if (ocp) transfers_issued++;
        submit(req);
        require(mixed_checker.evidence.size() == 1, "Expected exactly one actual SETUP, not queued intent/retries");
        response = mixed_checker.evidence[0].data;
        check_native(req, 1, response.size());
        mixed_checker.ocp_address_check_request(0, req, 1, discovery ? response : expected);
        if (snapshots_available) begin
            snapshot(after_dispatch, fw_configuration);
            // Normal usb_event_loop dispatch is reachable only from freshly
            // consumed EP0OUT notification, not polling the SETUP level.
            require(after_dispatch === before_dispatch + (ocp ? 32'd0 : 32'd1),
                    "Legacy notification-qualified dispatch delta / OCP dispatch exclusion failed");
            if (!ocp)
                require({observer_vif.get_snapshot_field(2), observer_vif.get_snapshot_field(1)} ===
                        mixed_checker.ocp_supersession_get_setup_line(req),
                        "MCU dispatched/snapshotted a different legacy SETUP");
            firmware_checks++;
        end
        if (ocp) claim_proof();
        close_window(1);
        checked_requests++;
    endtask

    protected task standard(input bit read_request, input logic [7:0] brequest,
        input logic [15:0] value, input int unsigned length, input string label,
        input logic [7:0] expected[$], output logic [7:0] response[$],
        input bit discovery = 0);
        svt_usb_transfer req;
        req = request(read_request, brequest, value, length, label);
        run_request(req, expected, response, discovery);
    endtask

    protected task check_configuration(input logic [7:0] value, input string label);
        logic [7:0] expected[$], response[$];
        logic [31:0] dispatches, fw_configuration;
        expected.push_back(value);
        standard(1, 8'h08, 0, 1, label, expected, response);
        snapshot(dispatches, fw_configuration);
        require(fw_configuration === {24'd0, value}, "Wire configuration and MCU configuration disagree");
        configuration_state = value;
        state_checks++;
        `uvm_info("SETUP_ADDRESS_STATE", $sformatf(
            "%s actual-address=%0d GET_CONFIGURATION=%0d firmware-config=%0d",
            label, dev_addr_v, value, fw_configuration), UVM_NONE)
    endtask

    protected task configure(input logic [7:0] value, input string label);
        logic [7:0] empty[$], response[$];
        standard(0, 8'h09, {8'd0, value}, 0, label, empty, response);
        check_configuration(value, {label, "_GET_CONFIGURATION"});
    endtask

    protected task discover_descriptors();
        logic [7:0] empty[$], header[$], blob[$];
        int total, offset, length, interfaces, functional;
        bit recovery_context;
        caliptra_ss_usb_shared_cfg shared_cfg;
        standard(1, 8'h06, 16'h0200, 9, "ADDRESS_CONFIG_HEADER", empty, header, 1);
        require((header.size() == 9) && (header[0] === 8'd9) && (header[1] === 8'd2) &&
                (header[5] !== 8'd0), "Invalid discovered configuration header");
        runtime_configuration = header[5];
        total = {header[3], header[2]};
        require((total >= 9) && (total <= 64),
                "Runtime configuration exceeds this testcase's single-packet checker budget");
        standard(1, 8'h06, 16'h0200, total, "ADDRESS_CONFIG_BLOB", empty, blob, 1);
        require(blob.size() == total, "Incomplete runtime configuration descriptors");
        foreach (header[i]) require(blob[i] === header[i], "Configuration header changed during discovery");
        interfaces = 0;
        functional = 0;
        recovery_context = 0;
        offset = 0;
        while (offset + 2 <= total) begin
            length = blob[offset];
            require((length >= 2) && (offset + length <= total), "Malformed descriptor framing");
            if (blob[offset + 1] === 8'h04) begin
                require(length == 9, "Invalid interface descriptor length");
                recovery_context = (blob[offset + 5] === 8'hEF) &&
                                   (blob[offset + 6] === 8'h08) &&
                                   (blob[offset + 7] === 8'h01);
                if (recovery_context) begin
                    require((blob[offset + 3] === 8'd0) && (blob[offset + 4] === 8'd0),
                            "OCP Recovery interface is not alternate zero / EP0-only");
                    runtime_interface = blob[offset + 2];
                    interfaces++;
                end
            end
            if ((blob[offset + 1] === OCP_USB_FUNC_DESC_TYPE) && recovery_context) begin
                require((length == OCP_USB_FUNC_DESC_LEN) &&
                        (blob[offset + OCP_OFF_UFD_SUBTYPE] === OCP_USB_FUNC_DESC_SUBTYPE) &&
                        (blob[offset + OCP_OFF_UFD_RESERVED] === 8'd0),
                        "Invalid OCP Recovery v1.1 8.5.3 functional descriptor");
                wMaxWrTransferSize = {blob[offset + OCP_OFF_UFD_MAX_WR_HI],
                                      blob[offset + OCP_OFF_UFD_MAX_WR_LO]};
                wMaxRdTransferSize = {blob[offset + OCP_OFF_UFD_MAX_RD_HI],
                                      blob[offset + OCP_OFF_UFD_MAX_RD_LO]};
                bcdOCPRecVersion = {blob[offset + OCP_OFF_UFD_BCD_VERSION_HI],
                                    blob[offset + OCP_OFF_UFD_BCD_VERSION_LO]};
                functional++;
            end
            offset += length;
        end
        require((offset == total) && (interfaces == 1) && (functional == 1),
                "No unique runtime Recovery interface/functional descriptor");
        require((wMaxWrTransferSize >= OCP_USB_MIN_TRANSFER_SIZE) &&
                (wMaxRdTransferSize == 64) && (bcdOCPRecVersion === OCP_USB_BCD_VERSION_1P1),
                "Unsupported runtime limits/version for bounded EP0 checker");
        require(uvm_config_db#(caliptra_ss_usb_shared_cfg)::get(null, "", "cfg", shared_cfg),
                "Shared observer classification config unavailable");
        shared_cfg.ocp_recovery_iface_num = runtime_interface;
        mixed_checker.recovery_interface = 16'(runtime_interface);
    endtask

    protected task discover_ocp();
        svt_usb_transfer req;
        logic [7:0] empty[$], response[$];
        bit [7:0] capability_response[$];
        req = request(1, OCP_BREQUEST_XFER, {8'd0, OCP_CMD_PROT_CAP},
                      wMaxRdTransferSize, "ADDRESS_DISCOVER_PROT_CAP", 1);
        run_request(req, empty, response, 1);
        foreach (response[i]) capability_response.push_back(response[i]);
        ocp_check_prot_cap_response(capability_response, "ADDRESS_DISCOVER_PROT_CAP");
        require(response.size() == OCP_SPEC_LEN_PROT_CAP, "Incomplete PROT_CAP discovery");
        ocp_bytes = response;
        req = request(1, OCP_BREQUEST_XFER, {8'd0, OCP_CMD_DEVICE_ID},
                      wMaxRdTransferSize, "ADDRESS_DISCOVER_DEVICE_ID", 1);
        run_request(req, empty, response, 1);
        require((response.size() >= OCP_SPEC_MIN_LEN_DEVICE_ID) &&
                (response.size() <= OCP_SPEC_MAX_LEN_DEVICE_ID),
                "Invalid runtime DEVICE_ID length");
        require(ocp_check_device_id_type(response[OCP_OFF_DID_DESC_TYPE]) &&
                (response.size() == OCP_OFF_DID_VENDOR_STRING +
                                    response[OCP_OFF_DID_VENDOR_STRING_LEN]),
                "Invalid OCP 1.1 DEVICE_ID descriptor format");
        device_id_bytes = response;
    endtask

    protected task interleave(input string label);
        svt_usb_transfer req;
        logic [7:0] expected[$], response[$];
        require(configuration_state === runtime_configuration,
                "Configured service requires restored runtime configuration");
        standard(1, 8'h06, 16'h0100, 18, {label, "_LEGACY18"}, descriptor_bytes, response);
        req = request(1, OCP_BREQUEST_XFER, {8'd0, OCP_CMD_PROT_CAP},
                      wMaxRdTransferSize, {label, "_PROT_CAP"}, 1);
        run_request(req, ocp_bytes, response);
        for (int i = 0; i < 8; i++) expected.push_back(descriptor_bytes[i]);
        standard(1, 8'h06, 16'h0100, 8, {label, "_LEGACY8"}, expected, response);
        req = request(1, OCP_BREQUEST_XFER, {8'd0, OCP_CMD_DEVICE_ID},
                      wMaxRdTransferSize, {label, "_DEVICE_ID"}, 1);
        run_request(req, device_id_bytes, response);
        service_groups++;
        `uvm_info("SETUP_ADDRESS_INTERLEAVE", {label, ": checked Configured L18/O-PC/L8/O-ID"}, UVM_NONE)
    endtask

    protected task set_address(input logic [6:0] new_address, input bit interrupt_status);
        svt_usb_transfer req;
        logic [31:0] before_dispatch, after_dispatch, fw_configuration;
        logic [31:0] in_descriptor;
        logic [7:0] empty[$], response[$];
        realtime old_setup_at;
        require(configuration_state === 8'd0, "SET_ADDRESS oracle requires proven Address/config0");
        snapshot(before_dispatch, fw_configuration);
        require(fw_configuration === 32'd0, "MCU was configured before SET_ADDRESS");
        req = request(0, 8'h05, {9'd0, new_address}, 0, "ADDRESS_HANDOFF_SET_ADDRESS");
        open_window();
        gate.ocp_address_configure_gate(req, wire_generation);
        fork : address_watchdog
            begin
                #(REQUEST_BOUND);
                `uvm_error("SETUP_ADDRESS_TIMEOUT", "SET_ADDRESS gate/retirement exceeded 100 us")
                `uvm_fatal("SETUP_ADDRESS_TIMEOUT", "No missing boundary credit")
            end
        join_none
        fork
            submit(req);
            begin
                wait (gate.termination_boundary_reached);
                require((mixed_checker.evidence.size() == 1) &&
                        (mixed_checker.evidence[0].generation === wire_generation) &&
                        (mixed_checker.evidence[0].setup_acks == 1) &&
                        (mixed_checker.evidence[0].setup_address === 7'(dev_addr_v)) &&
                        (mixed_checker.evidence[0].in_tokens == 0) &&
                        (mixed_checker.evidence[0].status_acks == 0),
                        "SET_ADDRESS never reached accepted old-address SETUP / pre-STATUS-IN boundary");
                // Allow the common handler to finish from its real EP0OUT
                // notification BEFORE interrupting, so this is not merely
                // cancelling an unserviced host queue entry.
                snapshot(after_dispatch, fw_configuration);
                require((after_dispatch === before_dispatch + 32'd1) &&
                        (fw_configuration === 32'd0) &&
                        ({observer_vif.get_snapshot_field(2), observer_vif.get_snapshot_field(1)} ===
                         mixed_checker.ocp_supersession_get_setup_line(req)),
                        "SET_ADDRESS lacks notification-qualified Address-state MCU dispatch");
                // Fixture command processing follows return from the common
                // event loop. Its fence iorw,iorw precedes command ACK, and
                // snapshot capture follows ACK withdrawal. Thus this same
                // generation sees the completed real SET_ADDRESS handler,
                // including its pending-address write and STATUS preparation.
                // usb.h EP command-list ABI: ACTIVE[31], DISABLED[30],
                // STALL[29], NBYTES[25:11]. This is stimulus readiness only;
                // never infer the correct host address from any MMIO value.
                in_descriptor = observer_vif.get_snapshot_field(
                    observer_vif.SNAPSHOT_FIELD_EP0_IN_DESC);
                require((in_descriptor[31] === 1'b1) &&
                        (in_descriptor[30:29] === 2'b00) &&
                        (in_descriptor[25:11] === 15'd0),
                        "Real SET_ADDRESS handler has not prepared/armed its zero-byte STATUS IN");
                require((mixed_checker.evidence[0].in_tokens == 0) &&
                        (mixed_checker.evidence[0].status_in_packets == 0) &&
                        (mixed_checker.evidence[0].status_acks == 0),
                        "STATUS escaped the pre-token gate before fenced preparation evidence");
                status_armed_checks++;
                `uvm_info("SETUP_ADDRESS_PREPARED", $sformatf(
                    "wire-gen=%0d command-gen=%0d decoded-SETUP=%016h dispatch=%0d->%0d IN-desc=%08h fenced-STATUS-armed=1 no-STATUS-token=1",
                    wire_generation, command_generation,
                    {observer_vif.get_snapshot_field(2), observer_vif.get_snapshot_field(1)},
                    before_dispatch, after_dispatch, in_descriptor), UVM_NONE)
                firmware_checks++;
                old_setup_at = mixed_checker.evidence[0].setup_ack_at;
                gate.ocp_termination_release_gate(wire_generation, interrupt_status);
                if (interrupt_status && !req.end_event.is_on()) req.abort(1'b1);
            end
        join
        gate.ocp_termination_check_and_retire_gate(wire_generation);
        disable address_watchdog;
        check_native(req, !interrupt_status, 0);
        mixed_checker.ocp_address_check_request(0, req, !interrupt_status, empty);
        checked_requests++;
        if (!interrupt_status) begin
            close_window(1);
            // No host endpoint traffic during the entire permitted address
            // recovery interval. SOFs remain enabled. This is not a reset.
            #(ADDRESS_RECOVERY);
            dev_addr_v = new_address;
            // Host context update is allowed ONLY after observed STATUS.
            // Never update a device CSR or repair an aborted VIP address table.
            usb_cfg.remote_device_cfg[0].device_address = new_address;
            host_agent_h.reconfigure(usb_cfg);
            mixed_checker.ocp_supersession_configure_acceptance_tracking(new_address);
            completed_changes++;
            check_configuration(0, "AFTER_COMPLETED_ADDRESS_AT_NEW");
        end else begin
            // abort(1) above releases only the serialized host worker. It is
            // NOT supersession evidence. Keep the same evidence generation;
            // submit a genuine GET_DESCRIPTOR SETUP to the OLD/current address.
            // No reconfigure/table rewrite is allowed on this branch.
            req = request(1, 8'h06, 16'h0100, 18, "ADDRESS_REPLACEMENT_AT_OLD");
            snapshot(before_dispatch, fw_configuration);
            submit(req);
            require(mixed_checker.evidence.size() == 2, "No actual replacement SETUP occurrence");
            response = mixed_checker.evidence[1].data;
            check_native(req, 1, response.size());
            mixed_checker.ocp_address_check_request(1, req, 1, descriptor_bytes);
            snapshot(after_dispatch, fw_configuration);
            require((after_dispatch === before_dispatch + 32'd1) &&
                    (fw_configuration === 32'd0) &&
                    ({observer_vif.get_snapshot_field(2), observer_vif.get_snapshot_field(1)} ===
                     mixed_checker.ocp_supersession_get_setup_line(req)),
                    "Replacement was not freshly dispatched in Address state");
            require((mixed_checker.evidence[0].in_tokens == 0) &&
                    (mixed_checker.evidence[0].status_in_packets == 0) &&
                    (mixed_checker.evidence[0].status_acks == 0) &&
                    (mixed_checker.evidence[1].setup_at > old_setup_at) &&
                    (mixed_checker.evidence[1].setup_acks == 1),
                    "Replacement did not interrupt SET_ADDRESS before any successful old STATUS");
            firmware_checks++;
            checked_requests++;
            close_window(2);
            interrupted_changes++;
            check_configuration(0, "AFTER_INTERRUPTED_ADDRESS_AT_OLD");
        end
        `uvm_info("SETUP_ADDRESS_HANDOFF", $sformatf(
            "new-value=%0d interrupted=%b wire-proven-current-address=%0d configuration=0",
            new_address, interrupt_status, dev_addr_v), UVM_NONE)
    endtask

    virtual task body();
        caliptra_ss_usb_ocp_setup_address_link_sequence link_seq;
        logic [7:0] empty[$], response[$], expected[$];
        logic [31:0] dispatches, fw_configuration;
        require(uvm_config_db#(caliptra_ss_usb_supersession_checker)::get(
            null, "", "usb_supersession_checker", mixed_checker), "Shared checker unavailable");
        require(uvm_config_db#(virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
            null, "uvm_test_top.env", "usb_legacy_ep0_observer_if", observer_vif),
            "MCU command observer unavailable");
        require(uvm_config_db#(virtual caliptra_ss_usb_supersession_csr_if)::get(
            null, "uvm_test_top.env", "usb_supersession_csr_if", csr), "Shared AXI adapter unavailable");
        require(uvm_config_db#(caliptra_ss_usb_stale_publication_protocol)::get(
            null, "", "usb_stale_publication_gate", gate), "Shared pre-token gate unavailable");
        csr.enabled = 0;
        csr.ocp_supersession_check_csr_map();
        resolve_xfer_handles(host_agent_h, usb_cfg, shared_status);
        dev_addr_v = 0;
        configuration_state = 0;
        mixed_checker.ocp_supersession_configure_acceptance_tracking(0);
        sof_baseline = mixed_checker.observed_sofs;
        command_generation = observer_vif.last_mcu_command_generation;
        require(command_generation === 16'd0, "Address fixture must begin in a fresh command epoch");
        // Direct initialization: cancelling a fork containing reconfigure()
        // would also kill persistent VIP descendants (including SOF workers).
        fork : initialization_watchdog
            begin
                #100ms;
                `uvm_error("SETUP_ADDRESS_TIMEOUT", "Ordinary link initialization exceeded 100 ms")
                `uvm_fatal("SETUP_ADDRESS_TIMEOUT", "Initial protocol stimulus missing")
            end
        join_none
        link_seq = caliptra_ss_usb_ocp_setup_address_link_sequence::type_id::create("address_link_seq");
        link_seq.start(p_sequencer, this);
        disable initialization_watchdog;

        // Real Default-state discovery, then 0->1 with STATUS at address 0.
        standard(1, 8'h06, 16'h0100, 18, "ADDRESS_ENUM_DEVICE_AT_ZERO", empty, response, 1);
        require((response.size() == 18) && (response[0] === 8'd18) &&
                (response[1] === 8'd1) && (response[7] === 8'd64) &&
                (response[17] !== 8'd0), "Invalid HS device descriptor discovery");
        descriptor_bytes = response;
        standard(0, 8'h05, 16'd1, 0, "ADDRESS_ENUM_SET_ONE", empty, response);
        #(ADDRESS_RECOVERY);
        dev_addr_v = 1;
        usb_cfg.remote_device_cfg[0].device_address = 1;
        host_agent_h.reconfigure(usb_cfg);
        mixed_checker.ocp_supersession_configure_acceptance_tracking(1);
        expected.push_back(0);
        standard(1, 8'h08, 0, 1, "ADDRESS_ENUM_CONFIG_ZERO", expected, response);
        standard(1, 8'h06, 16'h0100, 18, "ADDRESS_ENUM_DEVICE_AT_ONE", descriptor_bytes, response);
        discover_descriptors();
        standard(0, 8'h09, {8'd0, runtime_configuration}, 0,
                 "ADDRESS_ENUM_SET_RUNTIME_CONFIGURATION", empty, response);
        snapshots_available = 1;
        // Opcode 9/arg 3 already resumes the common USB event loop; no ABI
        // extension, address/config sideband write, or copied firmware stack.
        command(4'h9, 4'h3);
        check_configuration(runtime_configuration, "ADDRESS_ENUM_CONFIGURED");
        discover_ocp();
        interleave("BEFORE_ADDRESS_CHANGE");
        configure(0, "ENTER_ADDRESS_ONE");
        set_address(7'd2, 0);
        configure(runtime_configuration, "RESTORE_CONFIGURATION_AT_TWO");
        interleave("BETWEEN_ADDRESS_CHANGES");
        configure(0, "ENTER_ADDRESS_TWO");
        set_address(7'd3, 1);
        configure(runtime_configuration, "RESTORE_AFTER_INTERRUPTION_AT_TWO");
        interleave("AFTER_INTERRUPTED_ADDRESS");
        snapshot(dispatches, fw_configuration);
        require((fw_configuration === {24'd0, runtime_configuration}) &&
                (dev_addr_v == 2) && (completed_changes == 1) && (interrupted_changes == 1) &&
                (service_groups == 3) && (state_checks == 7) && (claim_checks == 8) &&
                (checked_requests == 35) && (checked_windows == 34) &&
                (mixed_checker.accepted_setups == 35) && (transfers_issued == 8) &&
                (firmware_checks == 28) && (dispatches === 32'd27) &&
                (status_armed_checks == 2) &&
                (mixed_checker.observed_sofs > sof_baseline),
                "Incomplete Address handoff stimulus/check inventory or SOF/configuration loss");
        `uvm_info("SETUP_ADDRESS_SUMMARY", $sformatf(
            "requests=%0d windows=%0d accepted=%0d firmware-checks=%0d claims=%0d states=%0d status-armed=%0d groups=%0d completed/interrupted=%0d/%0d SOFs=%0d final-address=%0d configuration=%0d",
            checked_requests, checked_windows, mixed_checker.accepted_setups, firmware_checks,
            claim_checks, state_checks, status_armed_checks, service_groups, completed_changes, interrupted_changes,
            mixed_checker.observed_sofs - sof_baseline, dev_addr_v, runtime_configuration), UVM_NONE)
        ocp_setup_publish_transfer_count();
        uvm_config_db#(bit)::set(null, "", "usb_setup_address_handoff_stimulus_completed", 1);
        // Inherited test teardown owns STOP, actual MCU halt and AXI drain.
    endtask
endclass
`endif
