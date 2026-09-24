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

`ifndef CALIPTRA_SS_USB_OCP_FIRMWARE_PROTOCOL_ERROR_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_FIRMWARE_PROTOCOL_ERROR_SEQUENCE_SV

// Firmware-originated PROTOCOL_ERROR_GENERAL (0xFF) validation.
// Coordinates with the validation firmware
//   src/integration/test_suites/cptra_usb_ocp_firmware_protocol_error/
// which:
//   1. Signals FW_PROTOCOL_ERROR_STATE_READY (0x51).
//   2. Polls CALIPTRA_STATUS.BATCH_ABORTED. On observing it, signals
//      FW_PROTOCOL_ERROR_STATE_BATCH_ABORTED_SEEN (0x52) with the path-disable bit.
//   3. Writes CALIPTRA_CTRL.OCP_PROTOCOL_ERROR_GENERAL, signals
//      FW_PROTOCOL_ERROR_STATE_GENERAL_REQ_SENT (0x53), and waits for the request bit
//      to self-clear.
//   4. Uses EXT reads to prove DEVICE_STATUS.PROT_ERROR reads are
//      non-destructive and stabilise at 0xFF; signals
//      FW_PROTOCOL_ERROR_STATE_PROT_ERROR_STABLE (0x54).
//   5. Signals FW_PROTOCOL_ERROR_STATE_DONE (0x55).
//
// Replacement-SETUP BATCH_ABORTED trigger:
//   A new SETUP during an incomplete FIFO write pulses
//   fifo_batch_abort, clears the OCP claim, and latches
//   CALIPTRA_STATUS.BATCH_ABORTED (sticky W1C). This sequence delivers
//   that stimulus without RTL or firmware changes:
//     (a) Configure INDIRECT_FIFO_CTRL for a modest image window so the
//         about-to-start INDIRECT_FIFO_DATA is a legal OCP claim.
//     (b) Arm the arbiter packet callback's live setup-stage-ACK event
//         (see caliptra_ss_usb_ocp_arbiter_packet_callback.svh::
//         arm_setup_ack_trigger()).
//     (c) Start a legal control-OUT INDIRECT_FIFO_DATA transfer sized to
//         wMaxWrTransferSize. At the moment its SETUP-stage RX ACK is
//         observed, the OCP arbiter owns an incomplete FIFO command with
//         zero committed words: the SETUP has been acknowledged but no
//         DATA/STATUS stages have run yet.
//     (d) Request a graceful svt_usb_transfer abort on the still-in-flight
//         transfer before its OUT DATA stage reaches the wire. Wait bounded
//         for item completion via the
//         host agent's NOTIFY_USB_TRANSFER_ENDED trigger.
//     (e) Immediately issue a valid unclaimed standard SETUP (GET
//         DESCRIPTOR CONFIG(0)). This is the on-wire replacement SETUP.
//         It must land while the previous FIFO command is still incomplete,
//         pulse
//         fifo_batch_abort, and clear the OCP claim.
//     (f) Wait for the durable firmware completion state, then run the
//         Recovery Agent read-and-clear pattern.
//
// VIP abort behavior:
//   svt_usb_transfer::abort(0) requests a graceful abort at a protocol-layer
//   clean break point. Two behaviors matter:
//     - Whether the OUT token / DATA0 payload of the aborted transfer
//       still reaches the wire before abort takes effect. The trigger
//       intent is that no OUT token is emitted, so the arbiter still
//       sees the FIFO command as incomplete when the replacement SETUP
//       arrives. If the VIP flushes the OUT token before honouring
//       abort, the FIFO command may complete or reject at DATA stage
//       instead of via replacement-SETUP; BATCH_ABORTED_SEEN will still
//       land provided the batch was not already retired before the
//       replacement SETUP arrives. Any miss
//       is surfaced through the firmware-state uvm_fatal, not a silent
//       pass.
//     - Whether NOTIFY_USB_TRANSFER_ENDED still fires after abort. In
//       every SVT USB VIP release inspected here it does, with the
//       transfer status set to ABORTED. The wait is nonetheless bounded
//       by the same FW_ERROR_ABORT_TIMEOUT budget so a hung abort is not
//       silently absorbed.

class caliptra_ss_usb_ocp_firmware_protocol_error_sequence
    extends caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_firmware_protocol_error_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    localparam int unsigned FW_ERROR_STATE_POLLS      = 20;
    localparam time         FW_ERROR_STATE_POLL_TICK  = 1us;

    // Setup-stage ACK, abort completion, and replacement-SETUP win each
    // get a 20us bounded window as instructed. USB Chapter 8 turn-around
    // budgets and SVT VIP scheduler latencies both fit inside this bound
    // by two orders of magnitude at full speed.
    localparam time FW_ERROR_TRIGGER_TIMEOUT = 20us;

    localparam logic [7:0] FW_PROTOCOL_ERROR_STATE_READY               = 8'h51;
    localparam logic [7:0] FW_PROTOCOL_ERROR_STATE_BATCH_ABORTED_SEEN  = 8'h52;
    localparam logic [7:0] FW_PROTOCOL_ERROR_STATE_GENERAL_REQ_SENT    = 8'h53;
    localparam logic [7:0] FW_PROTOCOL_ERROR_STATE_PROT_ERROR_STABLE   = 8'h54;
    localparam logic [7:0] FW_PROTOCOL_ERROR_STATE_DONE                = 8'h55;

    function new(string name =
        "caliptra_ss_usb_ocp_firmware_protocol_error_sequence");
        super.new(name);
    endfunction

    // Wait for a firmware state under a bounded poll budget. A missing
    // transition blocks all dependent checks, so fail immediately.
    protected virtual task expect_fw_state(
        input logic [7:0] target_state,
        input string label);
        bit found;
        semantics_vif.wait_for_fw_state_bounded(
            target_state, FW_ERROR_STATE_POLLS, FW_ERROR_STATE_POLL_TICK, found);
        if (!found) begin
            `uvm_fatal("OCP_FIRMWARE_ERROR",
                $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: firmware did not reach state 0x%02h ",
                           "(current fw_exec_ctrl[7:0]=0x%02h). See sequence ",
                           "header for the replacement-SETUP trigger contract."},
                          label, target_state,
                          semantics_vif.get_fw_state()))
        end else begin
            `uvm_info("OCP_FIRMWARE_ERROR",
                $sformatf("[FIRMWARE_PROTOCOL_ERROR] %s: observed firmware state 0x%02h.",
                          label, target_state), UVM_NONE)
        end
    endtask

    // Check that a DEVICE_STATUS response byte equals expected; treat a
    // truncated response as an actionable error.
    protected virtual function void check_prot_error_byte(
        input string label,
        ref bit [7:0] response[$],
        input bit [7:0] expected);

        if (response.size() <= OCP_OFF_DS_PROT_ERROR) begin
            `uvm_error("OCP_FIRMWARE_ERROR",
                $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: DEVICE_STATUS truncated to %0d bytes; ",
                           "PROT_ERROR unobservable."},
                          label, response.size()))
        end else if (response[OCP_OFF_DS_PROT_ERROR] != expected) begin
            `uvm_error("OCP_FIRMWARE_ERROR",
                $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: DEVICE_STATUS.PROT_ERROR=0x%02h ",
                           "expected 0x%02h."},
                          label, response[OCP_OFF_DS_PROT_ERROR], expected))
        end
    endfunction

    // Build a legal control-OUT INDIRECT_FIFO_DATA transfer sized to
    // wMaxWrTransferSize. The payload contents are deterministic so
    // debug on a captured trace remains simple.
    protected virtual function void build_fifo_data_transfer(
        input string label,
        output svt_usb_transfer req);

        int iface_num;
        int payload_size;

        iface_num = get_iface_num();
        payload_size = wMaxWrTransferSize;

        req = svt_usb_transfer::type_id::create({label, "_req"});
        if (usb_cfg != null) begin
            req.cfg = usb_cfg;
        end
        req.fix_anchors(0, 0, 0);
        req.payload = svt_usb_payload::type_id::create({label, "_payload"});
        if (req.payload == null) begin
            `uvm_fatal("OCP_FIRMWARE_ERROR",
                $sformatf("%s payload allocation failed", label))
        end
        req.payload.data = new[payload_size];

        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == dev_addr_v;
                setup_data_bmrequesttype_dir       == svt_usb_types::HOST_TO_DEVICE;
                setup_data_bmrequesttype_type      == svt_usb_types::CLASS;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_INTERFACE;
                setup_data_brequest                == OCP_BREQUEST_XFER;
                setup_data_w_value                 == {8'h00, OCP_CMD_INDIRECT_FIFO_DATA};
                setup_data_w_index                 == {8'h00, 8'(iface_num)};
                setup_data_w_length                == 16'(payload_size);
                payload_start_ix                   == 0;
                payload_intended_byte_count        == payload_size;
                payload.data.size()                == payload_size;
                foreach (payload.data[i]) payload.data[i] == 8'(i);
            }) begin
            `uvm_fatal("OCP_FIRMWARE_ERROR",
                $sformatf("%s transfer randomization failed", label))
        end
    endfunction

    // Runnable replacement-SETUP BATCH_ABORTED trigger.
    //
    // Reuses the arbiter packet-callback window so the post-trigger
    // proof can inspect packet records for (i) the original SETUP
    // sequence receiving its RX ACK and (ii) the replacement standard
    // GET_DESCRIPTOR transfer completing successfully.
    protected virtual task run_replacement_setup_trigger(
        input string label);

        svt_usb_transfer req;
        bit setup_ack_reached;
        bit transfer_completed;
        bit abort_completion_bounded;
        svt_usb_transfer replacement_req;

        build_fifo_data_transfer(label, req);

        checker.packet_callback.start_window(snapshot_generation);
        snapshot_generation++;
        checker.packet_callback.arm_setup_ack_trigger();

        setup_ack_reached = 1'b0;
        transfer_completed = 1'b0;
        abort_completion_bounded = 1'b0;

        // Issue the INDIRECT_FIFO_DATA control-OUT transfer in a forked
        // process so the parent can react to the SETUP-stage ACK and
        // cancel the item before its OUT DATA stage reaches the wire.
        fork : fw_error_trigger_worker
            begin
                start_item(req, -1, p_sequencer.xfer_sequencer);
                finish_item(req, -1);
                transfers_issued++;
                host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
                transfer_completed = 1'b1;
            end
        join_none

        checker.packet_callback.wait_for_setup_ack_trigger(
            FW_ERROR_TRIGGER_TIMEOUT, setup_ack_reached);
        if (!setup_ack_reached) begin
            disable fw_error_trigger_worker;
            req.abort(1'b0);
            `uvm_fatal("OCP_FIRMWARE_ERROR",
                $sformatf({"%s SETUP-stage ACK was not observed within %0t; ",
                           "OCP arbiter never entered the incomplete-FIFO ",
                           "command state so the replacement-SETUP trigger ",
                           "cannot land."},
                          label, FW_ERROR_TRIGGER_TIMEOUT))
        end
        `uvm_info("OCP_FIRMWARE_ERROR",
            $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: SETUP-stage ACK observed at %0t; ",
                       "aborting high-level control-OUT before OUT data stage."},
                      label, $realtime), UVM_NONE)

        // Cancel the high-level transfer before OUT data stage. The
        // abort call is idempotent; SVT VIP still fires
        // NOTIFY_USB_TRANSFER_ENDED with an ABORTED status. Wait bounded
        // so a hung abort surfaces rather than being silently absorbed.
        req.abort(1'b0);
        fork : fw_error_abort_wait
            begin
                wait (transfer_completed);
                abort_completion_bounded = 1'b1;
            end
            begin
                #(FW_ERROR_TRIGGER_TIMEOUT);
            end
        join_any
        disable fw_error_abort_wait;
        if (!abort_completion_bounded) begin
            disable fw_error_trigger_worker;
            `uvm_fatal("OCP_FIRMWARE_ERROR",
                $sformatf({"%s aborted transfer did not retire within %0t; ",
                           "cannot safely issue replacement SETUP."},
                          label, FW_ERROR_TRIGGER_TIMEOUT))
        end
        `uvm_info("OCP_FIRMWARE_ERROR",
            $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: aborted transfer retired at %0t with ",
                       "result %s."},
                      label, $realtime,
                      get_xfer_result(req).name()), UVM_NONE)

        // Issue a valid, unclaimed standard request. Only its SETUP ACK is
        // required: the replacement SETUP itself is the abort stimulus.
        replacement_req = svt_usb_transfer::type_id::create(
            {label, "_replacement_req"});
        start_item(replacement_req, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null) begin
            replacement_req.cfg = usb_cfg;
        end
        replacement_req.fix_anchors(0, 0, 0);
        if (!replacement_req.randomize() with {
                xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
                device_address == dev_addr_v;
                setup_data_bmrequesttype_dir == svt_usb_types::DEVICE_TO_HOST;
                setup_data_bmrequesttype_type == svt_usb_types::STANDARD;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
                setup_data_brequest == 8'h06;
                setup_data_w_value == 16'h0200;
                setup_data_w_index == 16'h0000;
                setup_data_w_length == 16'd9;
                payload_start_ix == 0;
                payload_intended_byte_count == 9;
            }) begin
            `uvm_fatal("OCP_FIRMWARE_ERROR",
                $sformatf("%s replacement SETUP randomization failed.", label))
        end
        finish_item(replacement_req, -1);
        host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();

        checker.packet_callback.stop_window();

        // Post-trigger proof from packet records: the original SETUP
        // sequence must have been ACKed, and the packet log must contain
        // at least two SETUP tokens (the original claimed OCP SETUP plus
        // the replacement standard SETUP).
        if (!checker.packet_callback.setup_stage_acked()) begin
            `uvm_error("OCP_FIRMWARE_ERROR",
                $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: no SETUP+DATA0+ACK sequence found in ",
                           "packet log; the original OCP SETUP did not reach ",
                           "the incomplete-command state."}, label))
        end
        if (checker.packet_callback.count_pid(
                svt_usb_packet::SETUP,
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_TX) < 2) begin
            `uvm_error("OCP_FIRMWARE_ERROR",
                $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: fewer than two TX SETUP tokens in the ",
                           "trigger window; replacement SETUP did not land."},
                          label))
        end
        if (checker.packet_callback.count_pid(
                svt_usb_packet::ACK,
                caliptra_ss_usb_ocp_arbiter_packet_callback::PACKET_RX) < 2) begin
            `uvm_error("OCP_FIRMWARE_ERROR",
                $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: replacement SETUP was not ACKed by ",
                           "the device."}, label))
        end
        `uvm_info("OCP_FIRMWARE_ERROR",
            $sformatf({"[FIRMWARE_PROTOCOL_ERROR] %s: trigger window completed with %0d packets ",
                       "and original+replacement SETUPs observed."},
                      label, checker.packet_callback.packet_count()),
            UVM_NONE)
    endtask

    virtual task body();
        bit [7:0] device_status[$];
        bit [7:0] second_status[$];
        bit [7:0] third_status[$];

        initialize_arbiter_transport();

        // Firmware must have reached READY before we drive the trigger.
        expect_fw_state(FW_PROTOCOL_ERROR_STATE_READY, "READY_BEFORE_TRIGGER");

        // Configure the FIFO region so the control-OUT INDIRECT_FIFO_DATA
        // transfer is a legal OCP claim rather than a pre-DATA reject.
        indirect_fifo_ctrl_write(
            8'h00, 1'b1, 32'h0000_0040, "FW_ERROR_FIFO_CTRL_RESET");
        indirect_fifo_ctrl_write(
            8'h00, 1'b0, 32'h0000_0040, "FW_ERROR_FIFO_CTRL_ARM");

        // Deliver the trigger via the canonical replacement-SETUP path.
        // No bus reset, no re-enumeration is required or performed.
        run_replacement_setup_trigger("FW_ERROR_TRIGGER_REPLACEMENT_SETUP");

        // Intermediate firmware states can complete while the replacement
        // transfer retires. The final state carries the observed error byte.
        expect_fw_state(
            FW_PROTOCOL_ERROR_STATE_DONE, "FIRMWARE_PROTOCOL_ERROR_DONE");
        if (semantics_vif.get_fw_data() != OCP_PROTOCOL_ERROR_GENERAL) begin
            `uvm_error("OCP_FIRMWARE_ERROR",
                $sformatf({"[FIRMWARE_PROTOCOL_ERROR] final firmware data=0x%02h, expected ",
                           "general protocol error 0x%02h."},
                          semantics_vif.get_fw_data(),
                          OCP_PROTOCOL_ERROR_GENERAL))
        end

        // USB RA read pattern: 0xFF present -> cleared on next read -> 0.
        device_status_read_and_check(device_status, "FW_ERROR_USB_STATUS_1");
        check_prot_error_byte(
            "FW_ERROR_USB_STATUS_1 first read", device_status,
            OCP_PROTOCOL_ERROR_GENERAL);

        device_status_read_and_check(second_status, "FW_ERROR_USB_STATUS_2");
        check_prot_error_byte(
            "FW_ERROR_USB_STATUS_2 cleared", second_status,
            OCP_PROTOCOL_ERROR_NONE);

        device_status_read_and_check(third_status, "FW_ERROR_USB_STATUS_3");
        check_prot_error_byte(
            "FW_ERROR_USB_STATUS_3 stable-zero", third_status,
            OCP_PROTOCOL_ERROR_NONE);

        publish_transfer_count();
        wait_mcu_axi_idle_before_finish("FW_ERROR_FINISH");

        `uvm_info("OCP_FIRMWARE_ERROR",
            "[FIRMWARE_PROTOCOL_ERROR] Firmware-originated 0xFF and clear-on-RA-read complete.",
            UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_FIRMWARE_PROTOCOL_ERROR_SEQUENCE_SV
