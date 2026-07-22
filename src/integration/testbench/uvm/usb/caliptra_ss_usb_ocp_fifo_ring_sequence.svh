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

`ifndef CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV

// =============================================================================
// caliptra_ss_usb_ocp_fifo_ring_sequence
//
// Directed OCP Recovery v1.1 Sec 8.2.5 FIFO-ring test:
//   * advertise FIFO_SIZE = 65 DWORDs and MAX_TRANSFER_SIZE = 64 DWORDs
//   * fill the 64-DWORD physical payload store
//   * verify the 65th unconsumed push is acknowledged but does not advance the
//     externally visible WRITE_INDEX
//   * pop one DWORD, confirm write-domain status conservatively lags the freed
//     slot, reject one immediate refill, then push a wrapped DWORD only after
//     the write-domain status exposes the free entry and drain through
//     READ_INDEX wrap
// TODO: This sequence is implemented directly against the RTL implementation, which
//       leaves potential for verification self-confirmation holes. This sequence
//       should be scrubbed of RTL references and operate strictly from spec compliance.
// =============================================================================
class caliptra_ss_usb_ocp_fifo_ring_sequence
    extends caliptra_ss_usb_ocp_recovery_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_fifo_ring_sequence)

    function new(string name = "caliptra_ss_usb_ocp_fifo_ring_sequence");
        super.new(name);
    endfunction

    virtual task body();
        caliptra_ss_usb_init_sequence init_seq;
        bit [7:0] cfg_blob[$];
        bit [7:0] resp_q[$];
        bit [7:0] recovery_ctrl_payload[$];
        bit [7:0] indir_fifo_ctrl_payload[$];
        bit [7:0] fifo_status[$];
        bit [7:0] fifo_data_resp[$];
        bit [7:0] image_chunk[$];
        bit [31:0] payload_dwords[$];
        bit [31:0] wrap_dword;
        int        poll_iter;
        int unsigned wr_idx;
        int unsigned rd_idx;
        bit          got_empty;
        bit          got_full;
        bit          slot_visible_seen;

        resolve_xfer_handles(host_agent_h, usb_cfg, shared_status);

        `uvm_info("OCPREC",
            "Starting directed INDIRECT_FIFO ring sequence from Configured state.",
            UVM_NONE)

        init_seq = caliptra_ss_usb_init_sequence::type_id::create("init_seq");
        init_seq.start(p_sequencer, this);

        get_cfg_desc(cfg_blob);
        parse_functional_descriptor(cfg_blob);
        if (!func_desc_found) begin
            `uvm_warning("OCPREC",
                "OCP_RECOVERY_FUNCTIONAL descriptor not found. Using 64-byte defaults for FIFO ring test.")
        end
        if (wMaxRdTransferSize < usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE) begin
            `uvm_error("OCPREC",
                $sformatf("wMaxRdTransferSize=%0d violates the OCP Recovery v1.1 Sec 8.5.1 minimum of %0d bytes.",
                          wMaxRdTransferSize, usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE))
            wMaxRdTransferSize = usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE;
        end
        if (wMaxWrTransferSize < usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE) begin
            `uvm_error("OCPREC",
                $sformatf("wMaxWrTransferSize=%0d violates the OCP Recovery v1.1 Sec 8.5.1 minimum of %0d bytes.",
                          wMaxWrTransferSize, usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE))
        end

        recovery_ctrl_payload.delete();
        recovery_ctrl_payload.push_back(8'h00);
        recovery_ctrl_payload.push_back(8'h00);
        recovery_ctrl_payload.push_back(8'h00);
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_RECOVERY_CTRL),
                       .wlength(16'(recovery_ctrl_payload.size())),
                       .payload_bytes(recovery_ctrl_payload),
                       .resp_bytes(resp_q),
                       .label("OCPREC_FIFO_RING_RECOVERY_CTRL"));

        indir_fifo_ctrl_payload.delete();
        indir_fifo_ctrl_payload.push_back(8'h00);
        indir_fifo_ctrl_payload.push_back(8'h01);
        indir_fifo_ctrl_payload.push_back(8'(usb_ocp_recovery_pkg::OCP_FIFO_RING_SIZE_DWORDS));
        indir_fifo_ctrl_payload.push_back(8'((usb_ocp_recovery_pkg::OCP_FIFO_RING_SIZE_DWORDS >> 8) & 'hFF));
        indir_fifo_ctrl_payload.push_back(8'((usb_ocp_recovery_pkg::OCP_FIFO_RING_SIZE_DWORDS >> 16) & 'hFF));
        indir_fifo_ctrl_payload.push_back(8'((usb_ocp_recovery_pkg::OCP_FIFO_RING_SIZE_DWORDS >> 24) & 'hFF));
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_CTRL),
                       .wlength(16'(indir_fifo_ctrl_payload.size())),
                       .payload_bytes(indir_fifo_ctrl_payload),
                       .resp_bytes(resp_q),
                       .label("OCPREC_FIFO_RING_CTRL"));

        read_fifo_status_and_check(.exp_empty(1),
                                   .exp_full(0),
                                   .exp_wr_idx(0),
                                   .exp_rd_idx(0),
                                   .label("OCPREC_FIFO_RING_STATUS_RESET"),
                                   .resp_bytes(fifo_status));

        payload_dwords.delete();
        for (int unsigned i = 0; i < usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS; i++) begin
            payload_dwords.push_back(32'hA5A50000 + i);
        end

        for (int chunk = 0; chunk < (usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS / (usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE / 4)); chunk++) begin
            image_chunk.delete();
            for (int word = 0; word < (usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE / 4); word++) begin
                bit [31:0] dword_v;
                dword_v = payload_dwords[(chunk * (usb_ocp_recovery_pkg::OCP_USB_MIN_TRANSFER_SIZE / 4)) + word];
                image_chunk.push_back(dword_v[7:0]);
                image_chunk.push_back(dword_v[15:8]);
                image_chunk.push_back(dword_v[23:16]);
                image_chunk.push_back(dword_v[31:24]);
            end
            ocp_class_xfer(.dir_in(1'b0),
                           .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_DATA),
                           .wlength(16'(image_chunk.size())),
                           .payload_bytes(image_chunk),
                           .resp_bytes(resp_q),
                           .label($sformatf("OCPREC_FIFO_RING_PUSH_%0d", chunk)));
        end

        read_fifo_status_and_check(.exp_empty(0),
                                   .exp_full(1),
                                   .exp_wr_idx(usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS),
                                   .exp_rd_idx(0),
                                   .label("OCPREC_FIFO_RING_STATUS_FULL"),
                                   .resp_bytes(fifo_status));

        wrap_dword = 32'hFACECAFE;
        image_chunk.delete();
        image_chunk.push_back(wrap_dword[7:0]);
        image_chunk.push_back(wrap_dword[15:8]);
        image_chunk.push_back(wrap_dword[23:16]);
        image_chunk.push_back(wrap_dword[31:24]);
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_DATA),
                       .wlength(16'(image_chunk.size())),
                       .payload_bytes(image_chunk),
                       .resp_bytes(resp_q),
                       .label("OCPREC_FIFO_RING_REJECTED_PUSH"));

        read_fifo_status_and_check(.exp_empty(0),
                                   .exp_full(1),
                                   .exp_wr_idx(usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS),
                                   .exp_rd_idx(0),
                                   .label("OCPREC_FIFO_RING_STATUS_REJECTED_PUSH"),
                                   .resp_bytes(fifo_status));

        read_fifo_data_and_check(.exp_dword(payload_dwords[0]),
                                 .label("OCPREC_FIFO_RING_POP_0"),
                                 .resp_bytes(fifo_data_resp));

        poll_iter = 0;
        slot_visible_seen = 1'b0;
        forever begin
            bit [7:0] empty_q[$];
            empty_q.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(fifo_status),
                           .label($sformatf("OCPREC_FIFO_RING_STATUS_POLL_%0d", poll_iter)));
            if (fifo_status.size() < 20) begin
                `uvm_error("OCPREC",
                    $sformatf("OCPREC_FIFO_RING_STATUS_POLL_%0d returned %0d bytes; need >= 20.",
                              poll_iter, fifo_status.size()))
                break;
            end
            wr_idx = {fifo_status[7], fifo_status[6], fifo_status[5], fifo_status[4]};
            rd_idx = {fifo_status[11], fifo_status[10], fifo_status[9], fifo_status[8]};
            got_empty = fifo_status[0][0];
            got_full  = fifo_status[0][1];
            if (wr_idx != usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS) begin
                `uvm_error("OCPREC",
                    $sformatf("Post-pop status changed WRITE_INDEX to %0d; expected %0d before refill.",
                              wr_idx, usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS))
                break;
            end
            if ((rd_idx == 0) && got_full && !got_empty) begin
                poll_iter++;
                if (poll_iter > 8) begin
                    `uvm_error("OCPREC",
                        "WRITE-domain FIFO status never exposed the freed slot within 8 polls.")
                    break;
                end
            end else if ((rd_idx == 1) && !got_full && !got_empty) begin
                slot_visible_seen = 1'b1;
                break;
            end else begin
                `uvm_error("OCPREC",
                    $sformatf("Unexpected conservative-lag status: EMPTY=%0d FULL=%0d WRITE_INDEX=%0d READ_INDEX=%0d.",
                              got_empty, got_full, wr_idx, rd_idx))
                break;
            end
        end

        if (!slot_visible_seen) begin
            `uvm_fatal("OCPREC",
                "WRITE-domain FIFO status never produced the expected post-pop visible free slot.")
        end

        image_chunk.delete();
        image_chunk.push_back(wrap_dword[7:0]);
        image_chunk.push_back(wrap_dword[15:8]);
        image_chunk.push_back(wrap_dword[23:16]);
        image_chunk.push_back(wrap_dword[31:24]);
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_DATA),
                       .wlength(16'(image_chunk.size())),
                       .payload_bytes(image_chunk),
                       .resp_bytes(resp_q),
                       .label("OCPREC_FIFO_RING_WRAP_PUSH_ACCEPTED"));

        read_fifo_status_and_check(.exp_empty(0),
                                   .exp_full(1),
                                   .exp_wr_idx(0),
                                   .exp_rd_idx(1),
                                   .label("OCPREC_FIFO_RING_STATUS_AFTER_ACCEPTED_REFILL"),
                                   .resp_bytes(fifo_status));

        for (int unsigned i = 1; i < usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS; i++) begin
            read_fifo_data_and_check(.exp_dword(payload_dwords[i]),
                                     .label($sformatf("OCPREC_FIFO_RING_POP_%0d", i)),
                                     .resp_bytes(fifo_data_resp));
        end
        read_fifo_data_and_check(.exp_dword(wrap_dword),
                                 .label("OCPREC_FIFO_RING_POP_WRAP_WORD"),
                                 .resp_bytes(fifo_data_resp));

        read_fifo_status_and_check(.exp_empty(1),
                                   .exp_full(0),
                                   .exp_wr_idx(0),
                                   .exp_rd_idx(0),
                                   .label("OCPREC_FIFO_RING_STATUS_EMPTY"),
                                   .resp_bytes(fifo_status));

        uvm_config_db#(int unsigned)::set(null, "*",
            "ocp_transfers_issued", transfers_issued);

        `uvm_info("OCPREC",
            "Directed INDIRECT_FIFO ring sequence complete.",
            UVM_NONE)
    endtask

    protected virtual task get_cfg_desc(ref bit [7:0] cfg_blob[$]);
        svt_usb_transfer creq;
        svt_usb_transfer creq2;
        bit [15:0] cfg_total_len;

        cfg_blob.delete();

        creq = svt_usb_transfer::type_id::create("OCPREC_FIFO_RING_GET_CONFIG_DESC_HDR_req");
        start_item(creq, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null) creq.cfg = usb_cfg;
        creq.fix_anchors(0, 0, 0);
        if (!creq.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == dev_addr_v;
                setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
                setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
                setup_data_brequest                == 8'h06;
                setup_data_w_value                 == 16'h0200;
                setup_data_w_index                 == 16'h0000;
                setup_data_w_length                == 16'd9;
                payload_intended_byte_count        == 16'd9;
            }) begin
            `uvm_fatal("OCPREC", "randomize failed for OCPREC_FIFO_RING_GET_CONFIG_DESC_HDR")
        end
        finish_item(creq, -1);
        host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        if ((creq.payload == null) || (creq.payload.data.size() < 9)) begin
            `uvm_fatal("OCPREC",
                "Configuration descriptor header read returned fewer than 9 bytes.")
        end

        cfg_total_len = {creq.payload.data[3], creq.payload.data[2]};

        creq2 = svt_usb_transfer::type_id::create("OCPREC_FIFO_RING_GET_CONFIG_DESC_FULL_req");
        start_item(creq2, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null) creq2.cfg = usb_cfg;
        creq2.fix_anchors(0, 0, 0);
        if (!creq2.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == dev_addr_v;
                setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
                setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
                setup_data_brequest                == 8'h06;
                setup_data_w_value                 == 16'h0200;
                setup_data_w_index                 == 16'h0000;
                setup_data_w_length                == cfg_total_len;
                payload_intended_byte_count        == cfg_total_len;
            }) begin
            `uvm_fatal("OCPREC", "randomize failed for OCPREC_FIFO_RING_GET_CONFIG_DESC_FULL")
        end
        finish_item(creq2, -1);
        host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        if (creq2.payload == null) begin
            `uvm_fatal("OCPREC",
                "Full configuration descriptor read returned a null payload.")
        end
        for (int i = 0; i < cfg_total_len; i++) begin
            cfg_blob.push_back(creq2.payload.data[i]);
        end
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_FIFO_RING_SEQUENCE_SV
