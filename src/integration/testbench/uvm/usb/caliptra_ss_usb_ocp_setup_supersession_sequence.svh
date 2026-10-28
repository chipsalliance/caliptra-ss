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

`ifndef CALIPTRA_SS_USB_OCP_SETUP_SUPERSESSION_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_SETUP_SUPERSESSION_SEQUENCE_SVH

// Waveform-oriented stimulus. Stage waits schedule host aborts, but do not
// establish packet-level supersession coverage or synchronize MCU service.
class caliptra_ss_usb_ocp_setup_supersession_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_setup_supersession_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    localparam time TRANSFER_TIMEOUT = 20us;
    localparam bit [7:0] GET_DESCRIPTOR = 8'h06;
    localparam bit [15:0] DEVICE_DESCRIPTOR = 16'h0100;
    localparam int unsigned DEVICE_DESCRIPTOR_BYTES = 18;

    function new(string name =
        "caliptra_ss_usb_ocp_setup_supersession_sequence");
        super.new(name);
    endfunction

    protected function svt_usb_transfer build_request(
        input bit ocp,
        input string label);
        svt_usb_transfer req;
        int unsigned length;
        int iface;

        req = svt_usb_transfer::type_id::create(label);
        req.cfg = usb_cfg;
        req.fix_anchors(0, 0, 0);
        length = ocp ? wMaxRdTransferSize : DEVICE_DESCRIPTOR_BYTES;
        iface = get_iface_num();
        // USB 2.0 9.4.3; OCP Recovery 1.1 8.5.1 read envelope.
        if (!req.randomize() with {
            xfer_type == svt_usb_transfer::CONTROL_TRANSFER;
            device_address == dev_addr_v;
            setup_data_bmrequesttype_dir == svt_usb_types::DEVICE_TO_HOST;
            setup_data_bmrequesttype_type ==
                (ocp ? svt_usb_types::CLASS : svt_usb_types::STANDARD);
            setup_data_bmrequesttype_recipient ==
                (ocp ? svt_usb_types::BMREQ_INTERFACE :
                       svt_usb_types::BMREQ_DEVICE);
            setup_data_brequest == (ocp ? OCP_BREQUEST_XFER : GET_DESCRIPTOR);
            setup_data_w_value ==
                (ocp ? {8'h00, OCP_CMD_PROT_CAP} : DEVICE_DESCRIPTOR);
            setup_data_w_index == (ocp ? 16'(iface) : 16'h0000);
            setup_data_w_length == 16'(length);
            payload_start_ix == 0;
            payload_intended_byte_count == length;
        }) begin
            `uvm_fatal("SETUP_SUPERSESSION",
                $sformatf("%s request randomization failed", label))
        end
        return req;
    endfunction

    protected task execute_request(
        input svt_usb_transfer req,
        input bit interrupt_request,
        input svt_usb_transfer::xfer_stage_enum completed_stage,
        input string label);
        bit retired;
        bit bounded;

        retired = 0;
        bounded = 0;
        `uvm_info("SETUP_SUPERSESSION",
            $sformatf("%s START interrupt=%0b boundary=%s at %0t",
                      label, interrupt_request, completed_stage.name(),
                      $realtime), UVM_NONE)
        fork : bounded_request
            begin
                fork
                    begin
                        uvm_object ended;
                        do begin
                            host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
                            ended = host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.get_trigger_data();
                        end while (ended != req);
                        retired = 1;
                    end
                    begin
                        start_item(req, -1, p_sequencer.xfer_sequencer);
                        finish_item(req, -1);
                    end
                    begin
                        if (interrupt_request) begin
                            req.wait_for_control_transfer_stage(
                                completed_stage, 1'b1);
                            `uvm_info("SETUP_SUPERSESSION",
                                $sformatf("%s boundary=%s at %0t; requesting immediate host abort",
                                          label, completed_stage.name(),
                                          $realtime), UVM_NONE)
                            // Stop at the observed completed transaction rather
                            // than letting graceful abort drain the next stage.
                            req.abort(1'b1);
                        end
                    end
                join
                bounded = 1;
            end
            begin
                #(TRANSFER_TIMEOUT);
            end
        join_any
        disable bounded_request;
        if (!bounded || !retired) begin
            req.abort(1'b1);
            `uvm_fatal("SETUP_SUPERSESSION",
                $sformatf("%s did not retire within %0t",
                          label, TRANSFER_TIMEOUT))
        end
        `uvm_info("SETUP_SUPERSESSION",
            $sformatf("%s END status=%s results=0x%0h at %0t",
                      label, req.status.name(), req.results_status,
                      $realtime), UVM_NONE)
        if (interrupt_request) begin
            if (get_xfer_result(req) != OCP_XFER_ABORTED) begin
                `uvm_error("SETUP_SUPERSESSION",
                    $sformatf("%s completed instead of being interrupted",
                              label))
            end
        end else if (get_xfer_result(req) != OCP_XFER_SUCCESS) begin
            `uvm_error("SETUP_SUPERSESSION",
                $sformatf("%s replacement did not complete successfully",
                          label))
        end
    endtask

    protected task run_scenario(
        input bit original_ocp,
        input svt_usb_transfer::xfer_stage_enum completed_stage,
        input string label);
        svt_usb_transfer original_req;
        svt_usb_transfer replacement_req;

        original_req = build_request(original_ocp, {label, "_original"});
        replacement_req = build_request(!original_ocp, {label, "_replacement"});
        execute_request(original_req, 1'b1, completed_stage,
                        {label, "_original"});
        if (original_ocp) transfers_issued++;
        execute_request(replacement_req, 1'b0, completed_stage,
                        {label, "_replacement"});
        if (!original_ocp) transfers_issued++;
        #1us;
    endtask

    virtual task body();
        initialize_ocp_transport();
        run_scenario(1'b0, svt_usb_transfer::SETUP_STAGE, "L_TO_O_DATA_PENDING");
        run_scenario(1'b1, svt_usb_transfer::SETUP_STAGE, "O_TO_L_DATA_PENDING");
        run_scenario(1'b0, svt_usb_transfer::DATA_STAGE, "L_TO_O_STATUS_PENDING");
        run_scenario(1'b1, svt_usb_transfer::DATA_STAGE, "O_TO_L_STATUS_PENDING");
        uvm_config_db#(int unsigned)::set(
            null, "", "ocp_transfers_issued", transfers_issued);
        `uvm_info("SETUP_SUPERSESSION",
            "All four raw supersession scenarios issued; inspect packet ordering in the waveform.",
            UVM_NONE)
    endtask
endclass

`endif
