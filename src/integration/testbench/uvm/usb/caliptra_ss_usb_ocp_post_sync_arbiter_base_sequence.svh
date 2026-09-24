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

`ifndef CALIPTRA_SS_USB_OCP_POST_SYNC_ARBITER_BASE_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_POST_SYNC_ARBITER_BASE_SEQUENCE_SV

class caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(
        caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected caliptra_ss_usb_ocp_arbiter_checker checker;
    protected virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
    protected virtual caliptra_ss_usb_ocp_access_semantics_if semantics_vif;
    protected logic [15:0] snapshot_generation;
    protected logic [15:0] path_generation;
    protected bit path_disabled;

    localparam time ARBITER_HANDSHAKE_TIMEOUT = 20ms;
    localparam int unsigned RESET_DURATION_TOLERANCE_PERCENT = 2;

    function new(string name =
        "caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence");
        super.new(name);
        snapshot_generation = 16'h0002;
        path_generation = 16'h0001;
        path_disabled = 1'b0;
    endfunction

    protected virtual function time configured_reset_duration();
        // Synopsys USB VIP timer reals are expressed in picoseconds.
        return $rtoi(usb_cfg.tdrst) * 1ps;
    endfunction

    protected virtual task initialize_arbiter_transport();
        bit ready;

        if (!uvm_config_db#(
                caliptra_ss_usb_ocp_arbiter_checker)::get(
                    null, "", "ocp_arbiter_checker", checker)) begin
            `uvm_fatal("OCP_ARB_SEQ",
                "ocp_arbiter_checker not found in config_db")
        end
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_fatal("OCP_ARB_SEQ",
                "usb_legacy_ep0_observer_if not found in config_db")
        end
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
                    null, "uvm_test_top.env",
                    "ocp_access_semantics_if", semantics_vif)) begin
            `uvm_fatal("OCP_ARB_SEQ",
                "ocp_access_semantics_if not found in config_db")
        end

        initialize_ocp_transport();
        observer_vif.issue_mcu_command_bounded(
            observer_vif.MCU_COMMAND_RELEASE_CALIPTRA,
            16'h0001,
            4'h0,
            ARBITER_HANDSHAKE_TIMEOUT,
            ready);
        if (!ready) begin
            `uvm_fatal("OCP_ARB_SEQ",
                "MCU did not acknowledge Caliptra release")
        end
        semantics_vif.wait_for_fw_state_generation_bounded(
            semantics_vif.FW_STATE_PATH_READY,
            16'h0000,
            ARBITER_HANDSHAKE_TIMEOUT,
            ready);
        if (!ready) begin
            `uvm_fatal("OCP_ARB_SEQ",
                "Caliptra PATH_READY generation 0 was not observed")
        end
    endtask

    protected virtual task open_observation_window(
        output logic [15:0] generation);

        bit acknowledged;
        bit ready;

        generation = snapshot_generation;
        snapshot_generation++;
        observer_vif.issue_mcu_command_bounded(
            observer_vif.MCU_COMMAND_PUBLISH_BASELINE,
            generation,
            4'h0,
            ARBITER_HANDSHAKE_TIMEOUT,
            acknowledged);
        if (!acknowledged) begin
            `uvm_fatal("OCP_ARB_SEQ",
                $sformatf("Baseline command generation %0d was not acknowledged",
                          generation))
        end
        checker.begin_observation(
            generation,
            path_disabled,
            ARBITER_HANDSHAKE_TIMEOUT,
            ready);
        if (!ready) begin
            `uvm_fatal("OCP_ARB_SEQ",
                $sformatf("Observation generation %0d did not open",
                          generation))
        end
    endtask

    protected virtual task close_observation_window(
        input logic [15:0] generation,
        input logic [3:0] expected_legacy_dispatch_delta);

        bit acknowledged;
        bit complete;

        observer_vif.issue_mcu_command_bounded(
            observer_vif.MCU_COMMAND_PUBLISH_POST,
            generation,
            expected_legacy_dispatch_delta,
            ARBITER_HANDSHAKE_TIMEOUT,
            acknowledged);
        if (!acknowledged) begin
            `uvm_fatal("OCP_ARB_SEQ",
                $sformatf("Post command generation %0d was not acknowledged",
                          generation))
        end
        checker.finish_observation(
            generation,
            ARBITER_HANDSHAKE_TIMEOUT,
            complete);
        if (!complete) begin
            `uvm_fatal("OCP_ARB_SEQ",
                $sformatf("Observation generation %0d did not close",
                          generation))
        end
    endtask

    protected virtual task run_claimed_read(
        input ocp_cmd_t command,
        input bit require_success,
        input string label);

        bit [7:0] response[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        run_claimed_read_length(
            command,
            16'(wMaxRdTransferSize),
            response,
            result,
            label);

        if ((result == OCP_XFER_ABORTED) && !path_disabled) begin
            `uvm_error("OCP_ARB_SEQ",
                $sformatf("%s was aborted", label))
        end
        if (require_success && (result != OCP_XFER_SUCCESS)) begin
            `uvm_error("OCP_ARB_SEQ",
                $sformatf("%s did not return a successful recovery response",
                          label))
        end
    endtask

    protected virtual task run_claimed_read_length(
        input ocp_cmd_t command,
        input bit [15:0] requested_length,
        ref bit [7:0] response[$],
        output caliptra_ss_usb_ocp_xfer_result_e result,
        input string label);

        logic [15:0] generation;
        bit [7:0] empty_payload[$];

        empty_payload.delete();
        open_observation_window(generation);
        ocp_class_xfer_result(
            1'b1,
            command,
            requested_length,
            empty_payload,
            response,
            result,
            label);
        close_observation_window(
            generation, path_disabled ? 4'h1 : 4'h0);
    endtask

    protected virtual function void require_setup_stage_ack(
        input string label);

        if (!checker.packet_callback.setup_stage_acked()) begin
            `uvm_error("OCP_ARB_SEQ",
                $sformatf("%s did not receive the mandatory SETUP-stage ACK",
                          label))
        end
    endfunction

    protected virtual function void report_packet_outcome(
        input string label);

        int unsigned nak_count;
        int unsigned stall_count;

        nak_count = checker.packet_callback.count_pid(
            svt_usb_packet::NAK,
            caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX);
        stall_count = checker.packet_callback.count_pid(
            svt_usb_packet::STALL,
            caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX);
        `uvm_info("OCP_ARB_PACKET",
            $sformatf("%s packets=%0d NAK=%0d STALL=%0d",
                      label,
                      checker.packet_callback.packet_count(),
                      nak_count,
                      stall_count),
            UVM_NONE)
    endfunction

    protected virtual task run_unclaimed_configuration_descriptor(
        input string label);

        logic [15:0] generation;
        bit [7:0] descriptor[$];

        open_observation_window(generation);
        standard_get_configuration_descriptor(9, descriptor, label);
        close_observation_window(generation, 4'h1);
        if (descriptor.size() != 9) begin
            `uvm_error("OCP_ARB_SEQ",
                $sformatf("%s returned %0d descriptor bytes, expected 9",
                          label, descriptor.size()))
        end
    endtask

    protected virtual task set_path_disable(input bit disabled);
        bit complete;
        logic [15:0] generation;

        generation = path_generation;
        path_generation++;
        semantics_vif.set_path_disable_bounded(
            disabled,
            generation,
            ARBITER_HANDSHAKE_TIMEOUT,
            complete);
        if (!complete) begin
            `uvm_fatal("OCP_ARB_SEQ",
                $sformatf("Path-disable command generation %0d failed",
                          generation))
        end
        path_disabled = disabled;
    endtask

    protected virtual task capture_legacy_snapshot(
        output logic [15:0] generation);

        bit acknowledged;
        bit captured;

        generation = snapshot_generation;
        snapshot_generation++;
        observer_vif.issue_mcu_command_bounded(
            observer_vif.MCU_COMMAND_PUBLISH_BASELINE,
            generation,
            4'h0,
            ARBITER_HANDSHAKE_TIMEOUT,
            acknowledged);
        if (!acknowledged) begin
            `uvm_fatal("OCP_ARB_SEQ",
                $sformatf("Snapshot command generation %0d was not acknowledged",
                          generation))
        end
        observer_vif.receive_snapshot(
            observer_vif.SNAPSHOT_STATE_BASELINE,
            generation,
            ARBITER_HANDSHAKE_TIMEOUT,
            captured);
        if (!captured) begin
            `uvm_fatal("OCP_ARB_SEQ",
                $sformatf("Snapshot generation %0d was not captured",
                          generation))
        end
    endtask

    protected virtual task capture_reset_post_snapshot(
        input logic [15:0] generation,
        input time timeout);

        bit acknowledged;
        bit captured;

        observer_vif.issue_mcu_command_bounded(
            observer_vif.MCU_COMMAND_PUBLISH_RESET_POST,
            generation,
            4'h1,
            timeout,
            acknowledged);
        if (!acknowledged) begin
            `uvm_fatal("OCP_ARB_006",
                $sformatf("Reset-post command generation %0d was not acknowledged",
                          generation))
        end
        observer_vif.receive_snapshot(
            observer_vif.SNAPSHOT_STATE_POST,
            generation,
            timeout,
            captured);
        if (!captured) begin
            `uvm_fatal("OCP_ARB_006",
                $sformatf({"Reset-post snapshot generation %0d was not ",
                           "captured because firmware did not observe the ",
                           "USB bus-reset counter advance"},
                          generation))
        end
    endtask

    protected virtual task reenumerate_after_reset();
        caliptra_ss_usb_init_sequence init_seq;

        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        init_seq = caliptra_ss_usb_init_sequence::type_id::create(
            "post_reset_init_seq");
        init_seq.post_reset_only = 1'b1;
        init_seq.start(p_sequencer, this);
        dev_addr_v = 1;
        discover_functional_descriptor();
    endtask

    protected virtual task run_reset_during_control_stage(
        input svt_usb_transfer::xfer_stage_enum target_stage,
        input string label);

        svt_usb_transfer req;
        svt_usb_link_service_20_command_sequence reset_seq;
        bit [7:0] empty_payload[$];
        bit stage_reached;
        bit reset_completed;
        bit transfer_completed;
        bit bounded_completion;
        bit stage_waiter_armed;
        bit reset_signal_observed;
        int iface_num;
        time observed_se0_duration;
        time expected_se0_duration;
        time reset_timeout;
        time minimum_se0_duration;
        time maximum_se0_duration;

        empty_payload.delete();
        iface_num = get_iface_num();
        req = svt_usb_transfer::type_id::create({label, "_req"});
        if (usb_cfg != null) begin
            req.cfg = usb_cfg;
        end
        req.fix_anchors(0, 0, 0);
        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == dev_addr_v;
                setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
                setup_data_bmrequesttype_type      == svt_usb_types::CLASS;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_INTERFACE;
                setup_data_brequest                == OCP_BREQUEST_XFER;
                setup_data_w_value                 == {8'h00, OCP_CMD_PROT_CAP};
                setup_data_w_index                 == {8'h00, 8'(iface_num)};
                setup_data_w_length                == wMaxRdTransferSize;
                payload_start_ix                   == 0;
                payload_intended_byte_count        == wMaxRdTransferSize;
            }) begin
            `uvm_fatal("OCP_ARB_006",
                $sformatf("%s transfer randomization failed", label))
        end

        checker.packet_callback.start_window(snapshot_generation);
        snapshot_generation++;
        stage_reached = 1'b0;
        reset_completed = 1'b0;
        transfer_completed = 1'b0;
        bounded_completion = 1'b0;
        stage_waiter_armed = 1'b0;
        reset_signal_observed = 1'b0;
        expected_se0_duration = configured_reset_duration();
        reset_timeout = expected_se0_duration * 4;
        minimum_se0_duration =
            expected_se0_duration *
            (100 - RESET_DURATION_TOLERANCE_PERCENT) / 100;
        maximum_se0_duration =
            expected_se0_duration *
            (100 + RESET_DURATION_TOLERANCE_PERCENT) / 100;

        fork : stage_reset_worker
            begin
                stage_waiter_armed = 1'b1;
                checker.packet_callback.wait_for_stage_trigger(
                    reset_timeout,
                    stage_reached);
                if (!stage_reached) begin
                    `uvm_fatal("OCP_ARB_006",
                        $sformatf("%s packet-stage trigger timed out", label))
                end
                reset_seq =
                    svt_usb_link_service_20_command_sequence::type_id::create(
                        {label, "_reset"});
                if (!reset_seq.randomize() with {
                        link_20_command_type ==
                            svt_usb_link_service::USB_20_PORT_RESET;
                        prereq_link_20_state ==
                            svt_usb_types::POWERED_OFF;
                    }) begin
                    `uvm_fatal("OCP_ARB_006",
                        $sformatf("%s reset sequence randomization failed",
                                  label))
                end
                observer_vif.arm_reset_signal_observation();
                fork : reset_execution
                    begin
                        reset_seq.start(
                            p_sequencer.link_service_sequencer);
                    end
                    begin
                        observer_vif.wait_for_reset_signal_bounded(
                            reset_timeout,
                            reset_signal_observed,
                            observed_se0_duration);
                    end
                join
                if (!reset_signal_observed) begin
                    `uvm_fatal("OCP_ARB_006",
                        $sformatf("%s did not produce an observable SE0 reset pulse",
                                  label))
                end
                reset_completed = 1'b1;
            end
        join_none
        wait (stage_waiter_armed);
        checker.packet_callback.arm_stage_trigger(target_stage);

        fork : bounded_reset_operation
            begin
                start_item(req, -1, p_sequencer.xfer_sequencer);
                finish_item(req, -1);
                transfers_issued++;
                host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
                transfer_completed = 1'b1;
                wait (reset_completed);
                bounded_completion = 1'b1;
            end
            begin
                #(reset_timeout);
            end
        join_any
        disable bounded_reset_operation;
        checker.packet_callback.stop_window();
        if (!bounded_completion) begin
            disable stage_reset_worker;
            req.abort(1'b1);
            `uvm_fatal("OCP_ARB_006",
                $sformatf({"%s did not complete within the bounded window: ",
                           "stage=%0b reset=%0b transfer=%0b"},
                          label,
                          stage_reached,
                          reset_completed,
                          transfer_completed))
        end
        if ((observed_se0_duration < minimum_se0_duration) ||
            (observed_se0_duration > maximum_se0_duration)) begin
            `uvm_fatal("OCP_ARB_006",
                $sformatf({"%s observed SE0 for %0t; configured tdrst=%0t ",
                           "with allowed range %0t..%0t"},
                          label,
                          observed_se0_duration,
                          expected_se0_duration,
                          minimum_se0_duration,
                          maximum_se0_duration))
        end
        `uvm_info("OCP_ARB_006",
            $sformatf("%s reset completed with transfer result %s and %0d packets",
                      label,
                      get_xfer_result(req).name(),
                      checker.packet_callback.packet_count()),
            UVM_NONE)
    endtask

endclass

class caliptra_ss_usb_ocp_arb_001_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_arb_001_sequence)

    function new(string name = "caliptra_ss_usb_ocp_arb_001_sequence");
        super.new(name);
    endfunction

    virtual task body();
        initialize_arbiter_transport();

        // OCP Recovery v1.1 Section 9.2 defines these commands as host-readable.
        // Mandatory commands must respond; optional capability reads may reject
        // the request while still remaining owned by the recovery path.
        run_claimed_read(OCP_CMD_PROT_CAP, 1'b1, "ARB001_PROT_CAP");
        run_claimed_read(OCP_CMD_DEVICE_ID, 1'b1, "ARB001_DEVICE_ID");
        run_claimed_read(OCP_CMD_DEVICE_STATUS, 1'b1, "ARB001_DEVICE_STATUS");
        run_claimed_read(OCP_CMD_RECOVERY_STATUS, 1'b1,
                         "ARB001_RECOVERY_STATUS");
        run_claimed_read(OCP_CMD_RECOVERY_CTRL, 1'b1,
                         "ARB001_RECOVERY_CTRL_READ");
        run_claimed_read(OCP_CMD_INDIRECT_FIFO_CTRL, 1'b1,
                         "ARB001_INDIRECT_FIFO_CTRL_READ");
        run_claimed_read(OCP_CMD_INDIRECT_FIFO_STATUS, 1'b1,
                         "ARB001_INDIRECT_FIFO_STATUS_READ");
        run_claimed_read(OCP_CMD_HW_STATUS, 1'b0, "ARB001_HW_STATUS");
        run_claimed_read(OCP_CMD_INDIRECT_CTRL, 1'b0,
                         "ARB001_INDIRECT_CTRL_READ");
        run_claimed_read(OCP_CMD_INDIRECT_STATUS, 1'b0,
                         "ARB001_INDIRECT_STATUS_READ");
        publish_transfer_count();
    endtask
endclass

class caliptra_ss_usb_ocp_arb_002_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_arb_002_sequence)

    function new(string name = "caliptra_ss_usb_ocp_arb_002_sequence");
        super.new(name);
    endfunction

    virtual task body();
        initialize_arbiter_transport();
        run_claimed_read(OCP_CMD_PROT_CAP, 1'b1, "ARB002_PROT_CAP_FIRST");
        run_unclaimed_configuration_descriptor("ARB002_CONFIG_SECOND");
        run_unclaimed_configuration_descriptor("ARB002_CONFIG_FIRST");
        run_claimed_read(OCP_CMD_DEVICE_ID, 1'b1,
                         "ARB002_DEVICE_ID_SECOND");
        `uvm_info("OCP_ARB_002",
            "Coverage gap: new-SETUP abandonment remains deferred.",
            UVM_NONE)
        publish_transfer_count();
    endtask
endclass

class caliptra_ss_usb_ocp_arb_003_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_arb_003_sequence)

    function new(string name = "caliptra_ss_usb_ocp_arb_003_sequence");
        super.new(name);
    endfunction

    virtual task body();
        initialize_arbiter_transport();

        // All phases use the same OCP Recovery v1.1 PROT_CAP read SETUP. Only
        // path ownership changes, so response payload equality is not assumed.
        run_claimed_read(OCP_CMD_PROT_CAP, 1'b1, "ARB003_ENABLED_FIRST");
        set_path_disable(1'b1);
        run_claimed_read(OCP_CMD_PROT_CAP, 1'b0, "ARB003_DISABLED");
        set_path_disable(1'b0);
        run_claimed_read(OCP_CMD_PROT_CAP, 1'b1, "ARB003_ENABLED_SECOND");
        publish_transfer_count();
    endtask
endclass

class caliptra_ss_usb_ocp_arb_004_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_arb_004_sequence)

    function new(string name = "caliptra_ss_usb_ocp_arb_004_sequence");
        super.new(name);
    endfunction

    virtual task body();
        bit [7:0] response[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        initialize_arbiter_transport();

        run_claimed_read_length(
            OCP_CMD_PROT_CAP,
            16'(wMaxRdTransferSize - 1),
            response,
            result,
            "ARB004_WRONG_READ_LENGTH");
        require_setup_stage_ack("ARB004_WRONG_READ_LENGTH");
        report_packet_outcome("ARB004_WRONG_READ_LENGTH");
        if (result == OCP_XFER_ABORTED) begin
            `uvm_error("OCP_ARB_004",
                "Wrong-length transfer aborted before a protocol response")
        end

        run_claimed_read_length(
            ocp_cmd_t'(8'hFF),
            16'(wMaxRdTransferSize),
            response,
            result,
            "ARB004_RESERVED_COMMAND");
        require_setup_stage_ack("ARB004_RESERVED_COMMAND");
        report_packet_outcome("ARB004_RESERVED_COMMAND");
        if (result == OCP_XFER_ABORTED) begin
            `uvm_error("OCP_ARB_004",
                "Reserved-command transfer aborted before a protocol response")
        end
        publish_transfer_count();
    endtask
endclass

class caliptra_ss_usb_ocp_arb_005_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_arb_005_sequence)

    function new(string name = "caliptra_ss_usb_ocp_arb_005_sequence");
        super.new(name);
    endfunction

    virtual task body();
        bit [7:0] response[$];
        bit [7:0] exact_response[$];
        caliptra_ss_usb_ocp_xfer_result_e result;
        int unsigned last_data_length;
        bit found_data;

        initialize_arbiter_transport();
        run_claimed_read_length(
            OCP_CMD_PROT_CAP,
            16'(wMaxRdTransferSize),
            response,
            result,
            "ARB005_SHORT_PROT_CAP");
        require_setup_stage_ack("ARB005_SHORT_PROT_CAP");
        if (result != OCP_XFER_SUCCESS) begin
            `uvm_error("OCP_ARB_005",
                "PROT_CAP short-response case did not complete successfully")
        end
        if ((response.size() == 0) ||
            (response.size() >= wMaxRdTransferSize)) begin
            `uvm_error("OCP_ARB_005",
                $sformatf("Expected a short PROT_CAP response below %0d bytes, got %0d",
                          wMaxRdTransferSize, response.size()))
        end
        found_data = checker.packet_callback.get_last_rx_data_length(
            last_data_length);
        if (!found_data || (last_data_length >= 64)) begin
            `uvm_error("OCP_ARB_005",
                $sformatf("Final PROT_CAP DATA packet was not short: found=%0b length=%0d",
                          found_data, last_data_length))
        end
        if (checker.packet_callback.count_zlp(
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) != 0) begin
            `uvm_error("OCP_ARB_005",
                "Short PROT_CAP response incorrectly used a terminating ZLP")
        end

        run_claimed_read_length(
            OCP_CMD_PROT_CAP,
            16'(response.size()),
            exact_response,
            result,
            "ARB005_EXACT_REQUEST_PROT_CAP");
        require_setup_stage_ack("ARB005_EXACT_REQUEST_PROT_CAP");
        if ((result != OCP_XFER_SUCCESS) ||
            (exact_response.size() != response.size())) begin
            `uvm_error("OCP_ARB_005",
                $sformatf("Exact-length PROT_CAP result=%s length=%0d expected=%0d",
                          result.name(),
                          exact_response.size(),
                          response.size()))
        end
        if (checker.packet_callback.count_zlp(
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) != 0) begin
            `uvm_error("OCP_ARB_005",
                "Exact-length PROT_CAP response incorrectly used a ZLP")
        end
        `uvm_info("OCP_ARB_005",
            {"Coverage gap: no current protocol-visible response constructs ",
             "returned_length < wLength with a returned length that is an ",
             "exact 64-byte multiple, so positive terminating-ZLP coverage ",
             "remains open."},
            UVM_NONE)
        publish_transfer_count();
    endtask
endclass

class caliptra_ss_usb_ocp_arb_006_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_arb_006_sequence)

    function new(string name = "caliptra_ss_usb_ocp_arb_006_sequence");
        super.new(name);
    endfunction

    protected virtual task run_reset_variant(
        input svt_usb_transfer::xfer_stage_enum target_stage,
        input string label);

        logic [15:0] before_generation;
        logic [31:0] before_reset_count;
        logic [31:0] after_reset_count;

        capture_legacy_snapshot(before_generation);
        before_reset_count = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_BUS_RESET_COUNT);
        run_reset_during_control_stage(target_stage, label);
        capture_reset_post_snapshot(
            before_generation,
            configured_reset_duration() * 4);
        after_reset_count = observer_vif.get_snapshot_field(
            observer_vif.SNAPSHOT_FIELD_BUS_RESET_COUNT);
        if (after_reset_count <= before_reset_count) begin
            `uvm_fatal("OCP_ARB_006",
                $sformatf("%s bus-reset count did not advance: %0d -> %0d",
                          label, before_reset_count, after_reset_count))
        end
        reenumerate_after_reset();
        run_claimed_read(
            OCP_CMD_PROT_CAP,
            1'b1,
            {label, "_POST_RESET_PROT_CAP"});
    endtask

    virtual task body();
        initialize_arbiter_transport();
        run_reset_variant(
            svt_usb_transfer::SETUP_STAGE,
            "ARB006_SETUP_STAGE");
        run_reset_variant(
            svt_usb_transfer::DATA_STAGE,
            "ARB006_DATA_STAGE");
        run_reset_variant(
            svt_usb_transfer::STATUS_STAGE,
            "ARB006_STATUS_STAGE");
        publish_transfer_count();
    endtask
endclass

class caliptra_ss_usb_ocp_arb_007_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_arb_007_sequence)

    function new(string name = "caliptra_ss_usb_ocp_arb_007_sequence");
        super.new(name);
    endfunction

    virtual task body();
        bit [7:0] response[$];
        bit [7:0] empty_payload[$];
        caliptra_ss_usb_ocp_xfer_result_e result;
        bit phase_valid;
        bit setup_found;
        bit phase_bins[string];
        bit utmi_bins[int unsigned];
        bit core_bins[int unsigned];
        logic [15:0] generation;
        realtime setup_time;
        time utmi_phase;
        time core_phase;
        time utmi_period;
        time core_period;
        int unsigned utmi_bucket;
        int unsigned core_bucket;
        string phase_key;

        initialize_arbiter_transport();
        for (int unsigned phase_index = 0;
             phase_index < 8;
             phase_index++) begin
            empty_payload.delete();
            open_observation_window(generation);
            observer_vif.wait_launch_phase(phase_index);
            ocp_class_xfer_result(
                1'b1,
                OCP_CMD_PROT_CAP,
                16'(wMaxRdTransferSize),
                empty_payload,
                response,
                result,
                $sformatf("ARB007_PHASE_%0d", phase_index));
            close_observation_window(generation, 4'h0);
            require_setup_stage_ack(
                $sformatf("ARB007_PHASE_%0d", phase_index));
            if (result != OCP_XFER_SUCCESS) begin
                `uvm_error("OCP_ARB_007",
                    $sformatf("Arrival phase %0d did not complete successfully",
                              phase_index))
            end
            setup_found =
                checker.packet_callback.get_setup_timestamp(setup_time);
            phase_valid = setup_found &&
                observer_vif.get_setup_clock_phases(
                    setup_time,
                    utmi_phase,
                    core_phase,
                    utmi_period,
                    core_period);
            if (!phase_valid) begin
                `uvm_error("OCP_ARB_007",
                    $sformatf("Arrival phase %0d lacks a valid SETUP timestamp",
                              phase_index))
                continue;
            end
            utmi_bucket = (utmi_phase * 4) / utmi_period;
            core_bucket = (core_phase * 4) / core_period;
            phase_key = $sformatf("%0d:%0d", utmi_bucket, core_bucket);
            phase_bins[phase_key] = 1'b1;
            utmi_bins[utmi_bucket] = 1'b1;
            core_bins[core_bucket] = 1'b1;
            `uvm_info("OCP_ARB_007",
                $sformatf({"Clock-arrival stress request bin %0d completed: ",
                           "SETUP completion UTMI phase=%0t/%0t bucket=%0d ",
                           "core phase=%0t/%0t bucket=%0d"},
                          phase_index,
                          utmi_phase,
                          utmi_period,
                          utmi_bucket,
                          core_phase,
                          core_period,
                          core_bucket),
                UVM_NONE)
        end
        if ((phase_bins.num() < 4) ||
            (utmi_bins.num() < 2) ||
            (core_bins.num() < 2)) begin
            `uvm_error("OCP_ARB_007",
                $sformatf({"Measured SETUP completion coverage is insufficient: ",
                           "pairs=%0d UTMI_quarters=%0d core_quarters=%0d"},
                          phase_bins.num(),
                          utmi_bins.num(),
                          core_bins.num()))
        end
        publish_transfer_count();
    endtask
endclass

`endif // CALIPTRA_SS_USB_OCP_POST_SYNC_ARBITER_BASE_SEQUENCE_SV
