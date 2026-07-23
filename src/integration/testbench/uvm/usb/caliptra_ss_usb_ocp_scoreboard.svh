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

`ifndef CALIPTRA_SS_USB_OCP_SCOREBOARD_SV
`define CALIPTRA_SS_USB_OCP_SCOREBOARD_SV

// Passive OCP Recovery checker. FIFO expectations use only OCP-visible
// transfers and runtime INDIRECT_FIFO_STATUS capabilities.
class caliptra_ss_usb_ocp_scoreboard extends uvm_component;

    `uvm_component_utils(caliptra_ss_usb_ocp_scoreboard)

    uvm_analysis_imp #(svt_usb_transfer, caliptra_ss_usb_ocp_scoreboard)
        transfer_imp;

    protected bit [7:0] pending_fifo_bytes[$];
    protected int unsigned pending_write_dwords[$];
    protected bit [7:0] committed_fifo_bytes[$];

    protected bit          fifo_baseline_valid;
    protected bit          fifo_caps_valid;
    protected int unsigned expected_write_index;
    protected int unsigned actual_read_index;
    protected int unsigned visible_read_index;
    protected int unsigned fifo_size;
    protected int unsigned max_transfer_dwords;
    protected bit [7:0]    region_type;

    protected int unsigned xfer_count[bit[7:0]][2];
    protected int unsigned total_class_xfers;
    protected int unsigned total_nonsuccess_xfers;
    protected int unsigned total_prot_cap_in;
    protected int unsigned total_prot_cap_mismatch;
    protected int unsigned total_fifo_data_out_bytes;
    protected int unsigned total_fifo_data_in;
    protected int unsigned total_fifo_status_in;
    protected int unsigned total_fifo_rejected_dwords;
    protected int unsigned total_fifo_external_reads;

    function new(string name = "caliptra_ss_usb_ocp_scoreboard",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        transfer_imp = new("transfer_imp", this);
        reset_fifo_model();
        total_class_xfers          = 0;
        total_nonsuccess_xfers     = 0;
        total_prot_cap_in          = 0;
        total_prot_cap_mismatch    = 0;
        total_fifo_data_out_bytes  = 0;
        total_fifo_data_in         = 0;
        total_fifo_status_in       = 0;
        total_fifo_rejected_dwords = 0;
        total_fifo_external_reads  = 0;
    endfunction

    protected virtual function void reset_fifo_model();
        pending_fifo_bytes.delete();
        pending_write_dwords.delete();
        committed_fifo_bytes.delete();
        fifo_baseline_valid = 1'b1;
        fifo_caps_valid     = 1'b0;
        expected_write_index = 0;
        actual_read_index    = 0;
        visible_read_index   = 0;
        fifo_size            = 0;
        max_transfer_dwords  = 0;
        region_type          = OCP_REGION_RECOVERY_CODE_WO;
    endfunction

    protected virtual function bit is_xfer_successful(
        svt_usb_transfer transfer);
        return caliptra_ss_usb_xfer_successful(transfer);
    endfunction

    protected virtual function int unsigned ring_distance(
        input int unsigned from_index,
        input int unsigned to_index);
        if (fifo_size == 0) return 0;
        return (to_index + fifo_size - from_index) % fifo_size;
    endfunction

    protected virtual function int unsigned observed_occupancy(
        input int unsigned write_index,
        input int unsigned read_index);
        if (fifo_size == 0) return 0;
        return (write_index + fifo_size - read_index) % fifo_size;
    endfunction

    protected virtual function bit valid_payload_window(
        input svt_usb_transfer transfer,
        output int start_index,
        output int end_index);
        start_index = 0;
        end_index = 0;
        if ((transfer == null) || (transfer.payload == null)) return 1'b0;
        start_index = transfer.payload_start_ix;
        end_index = transfer.payload_end_ix;
        if ((start_index < 0) || (end_index < start_index) ||
            (end_index > transfer.payload.data.size())) return 1'b0;
        return 1'b1;
    endfunction

    protected virtual function void queue_fifo_write_attempt(
        input svt_usb_transfer transfer);
        int start_index;
        int end_index;
        int unsigned delivered_bytes;
        int unsigned delivered_dwords;

        if (!valid_payload_window(transfer, start_index, end_index)) begin
            `uvm_error("OCPREC_MARK",
                "INDIRECT_FIFO_DATA OUT has an invalid payload window.")
            return;
        end
        delivered_bytes = end_index - start_index;
        if (delivered_bytes < transfer.setup_data_w_length) begin
            `uvm_info("OCPREC_MARK",
                $sformatf("INDIRECT_FIFO_DATA OUT delivered %0d of %0d requested bytes; FIFO candidate model unchanged.",
                          delivered_bytes, transfer.setup_data_w_length),
                UVM_NONE)
            return;
        end
        if ((transfer.setup_data_w_length % 4) != 0) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("INDIRECT_FIFO_DATA OUT length=%0d is not DWORD aligned.",
                          transfer.setup_data_w_length))
            return;
        end

        delivered_dwords = transfer.setup_data_w_length / 4;
        for (int unsigned i = 0;
             i < transfer.setup_data_w_length; i++) begin
            pending_fifo_bytes.push_back(
                transfer.payload.data[start_index + i]);
        end
        pending_write_dwords.push_back(delivered_dwords);
        total_fifo_data_out_bytes += transfer.setup_data_w_length;
    endfunction

    protected virtual function void reconcile_fifo_writes(
        input int unsigned observed_write_index);
        int unsigned advanced_dwords;
        int unsigned pending_dwords;
        int unsigned accepted_bytes;

        pending_dwords = pending_fifo_bytes.size() / 4;
        advanced_dwords =
            ring_distance(expected_write_index, observed_write_index);
        if (advanced_dwords > pending_dwords) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("WRITE_INDEX advanced by %0d DWORDs with only %0d pending observed DWORDs.",
                          advanced_dwords, pending_dwords))
            advanced_dwords = pending_dwords;
        end

        accepted_bytes = advanced_dwords * 4;
        for (int unsigned i = 0; i < accepted_bytes; i++) begin
            committed_fifo_bytes.push_back(
                pending_fifo_bytes.pop_front());
        end
        total_fifo_rejected_dwords +=
            (pending_fifo_bytes.size() / 4);
        pending_fifo_bytes.delete();
        pending_write_dwords.delete();
        expected_write_index = observed_write_index;
    endfunction

    protected virtual function void check_fifo_data_read(
        input svt_usb_transfer transfer);
        int start_index;
        int end_index;
        bit [7:0] expected_byte;

        if (!valid_payload_window(transfer, start_index, end_index) ||
            ((end_index - start_index) < 4)) begin
            `uvm_error("OCPREC_MARK",
                "INDIRECT_FIFO_DATA IN did not contain one complete DWORD.")
            return;
        end
        if (committed_fifo_bytes.size() < 4) begin
            `uvm_error("OCPREC_MARK",
                "INDIRECT_FIFO_DATA IN observed while the protocol model is empty.")
            return;
        end

        for (int unsigned i = 0; i < 4; i++) begin
            expected_byte = committed_fifo_bytes.pop_front();
            if (transfer.payload.data[start_index + i] !== expected_byte) begin
                `uvm_error("OCPREC_MARK",
                    $sformatf("INDIRECT_FIFO_DATA byte %0d mismatch: expected 0x%02h got 0x%02h.",
                              i, expected_byte,
                              transfer.payload.data[start_index + i]))
            end
        end
        if (fifo_caps_valid)
            actual_read_index = (actual_read_index + 1) % fifo_size;
        total_fifo_data_in++;
    endfunction

    protected virtual function void check_fifo_status(
        input svt_usb_transfer transfer);
        int start_index;
        int end_index;
        int unsigned observed_write_index;
        int unsigned observed_read_index;
        int unsigned observed_fifo_size;
        int unsigned observed_max_transfer;
        int unsigned occupancy;
        int unsigned space;
        int unsigned pending_visible_pops;
        int unsigned observed_pop_advance;
        int unsigned external_pop_dwords;
        bit observed_empty;
        bit observed_full;

        if (!valid_payload_window(transfer, start_index, end_index) ||
            ((end_index - start_index) <
                OCP_SPEC_LEN_INDIRECT_FIFO_STATUS)) begin
            `uvm_error("OCPREC_MARK",
                "INDIRECT_FIFO_STATUS IN payload is incomplete.")
            return;
        end

        observed_empty =
            (transfer.payload.data[start_index + OCP_OFF_IFS_STATUS] &
             OCP_IFS_EMPTY_MASK) != 0;
        observed_full =
            (transfer.payload.data[start_index + OCP_OFF_IFS_STATUS] &
             OCP_IFS_FULL_MASK) != 0;
        region_type =
            transfer.payload.data[start_index + OCP_OFF_IFS_REGION_TYPE];
        observed_write_index = {
            transfer.payload.data[start_index + OCP_OFF_IFS_WRITE_INDEX_B3],
            transfer.payload.data[start_index + OCP_OFF_IFS_WRITE_INDEX_B3-1],
            transfer.payload.data[start_index + OCP_OFF_IFS_WRITE_INDEX_B0+1],
            transfer.payload.data[start_index + OCP_OFF_IFS_WRITE_INDEX_B0]};
        observed_read_index = {
            transfer.payload.data[start_index + OCP_OFF_IFS_READ_INDEX_B3],
            transfer.payload.data[start_index + OCP_OFF_IFS_READ_INDEX_B3-1],
            transfer.payload.data[start_index + OCP_OFF_IFS_READ_INDEX_B0+1],
            transfer.payload.data[start_index + OCP_OFF_IFS_READ_INDEX_B0]};
        observed_fifo_size = {
            transfer.payload.data[start_index + OCP_OFF_IFS_FIFO_SIZE_B3],
            transfer.payload.data[start_index + OCP_OFF_IFS_FIFO_SIZE_B3-1],
            transfer.payload.data[start_index + OCP_OFF_IFS_FIFO_SIZE_B0+1],
            transfer.payload.data[start_index + OCP_OFF_IFS_FIFO_SIZE_B0]};
        observed_max_transfer = {
            transfer.payload.data[start_index + OCP_OFF_IFS_MAX_TRANSFER_B3],
            transfer.payload.data[start_index + OCP_OFF_IFS_MAX_TRANSFER_B3-1],
            transfer.payload.data[start_index + OCP_OFF_IFS_MAX_TRANSFER_B0+1],
            transfer.payload.data[start_index + OCP_OFF_IFS_MAX_TRANSFER_B0]};

        if ((observed_fifo_size < 2) ||
            (observed_max_transfer == 0)) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("INDIRECT_FIFO_STATUS advertises FIFO_SIZE=%0d MAX_TRANSFER_SIZE=%0d; expected FIFO_SIZE>=2 and nonzero transfer size.",
                          observed_fifo_size, observed_max_transfer))
            return;
        end
        if ((observed_write_index >= observed_fifo_size) ||
            (observed_read_index >= observed_fifo_size)) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("INDIRECT_FIFO_STATUS index out of range: W=%0d R=%0d SIZE=%0d.",
                          observed_write_index, observed_read_index,
                          observed_fifo_size))
            return;
        end

        if (!fifo_caps_valid) begin
            fifo_size = observed_fifo_size;
            max_transfer_dwords = observed_max_transfer;
            if (!fifo_baseline_valid) begin
                expected_write_index = observed_write_index;
                actual_read_index = observed_read_index;
                visible_read_index = observed_read_index;
                pending_fifo_bytes.delete();
                pending_write_dwords.delete();
            end
            fifo_caps_valid = 1'b1;
        end else begin
            if ((observed_fifo_size != fifo_size) ||
                (observed_max_transfer != max_transfer_dwords)) begin
                `uvm_error("OCPREC_MARK",
                    $sformatf("FIFO capabilities changed: SIZE %0d->%0d MAX_TRANSFER %0d->%0d.",
                              fifo_size, observed_fifo_size,
                              max_transfer_dwords,
                              observed_max_transfer))
            end
        end

        foreach (pending_write_dwords[i]) begin
            if (pending_write_dwords[i] > max_transfer_dwords) begin
                `uvm_error("OCPREC_MARK",
                    $sformatf("FIFO DATA attempt %0d contains %0d DWORDs, exceeding advertised MAX_TRANSFER_SIZE=%0d.",
                              i, pending_write_dwords[i],
                              max_transfer_dwords))
            end
        end
        reconcile_fifo_writes(observed_write_index);

        pending_visible_pops =
            ring_distance(visible_read_index, actual_read_index);
        observed_pop_advance =
            ring_distance(visible_read_index, observed_read_index);
        if (observed_pop_advance > pending_visible_pops) begin
            external_pop_dwords =
                observed_pop_advance - pending_visible_pops;
            if (committed_fifo_bytes.size() <
                    (external_pop_dwords * 4)) begin
                `uvm_error("OCPREC_MARK",
                    $sformatf("READ_INDEX reports %0d externally consumed DWORDs, but only %0d modeled DWORDs remain.",
                              external_pop_dwords,
                              committed_fifo_bytes.size() / 4))
                committed_fifo_bytes.delete();
            end else begin
                repeat (external_pop_dwords * 4)
                    void'(committed_fifo_bytes.pop_front());
            end
            actual_read_index =
                (actual_read_index + external_pop_dwords) % fifo_size;
            total_fifo_external_reads += external_pop_dwords;
        end
        visible_read_index = observed_read_index;

        occupancy =
            observed_occupancy(observed_write_index, observed_read_index);
        space = observed_fifo_size - 1 - occupancy;
        if (observed_empty !== (occupancy == 0)) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("EMPTY=%0b conflicts with occupancy=%0d.",
                          observed_empty, occupancy))
        end
        if (observed_full !== (space == 0)) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("FULL=%0b conflicts with available space=%0d.",
                          observed_full, space))
        end
        if (region_type == OCP_REGION_RECOVERY_CODE_WO) begin
            int unsigned actual_occupancy;
            actual_occupancy = committed_fifo_bytes.size() / 4;
            if ((occupancy < actual_occupancy) ||
                (occupancy > (actual_occupancy +
                    ring_distance(visible_read_index,
                                  actual_read_index)))) begin
                `uvm_error("OCPREC_MARK",
                    $sformatf("Visible occupancy=%0d is inconsistent with modeled occupancy=%0d and pending read visibility.",
                              occupancy, actual_occupancy))
            end
        end
        total_fifo_status_in++;
    endfunction

    virtual function void write(svt_usb_transfer transfer);
        bit [7:0] cmd_code;
        bit dir_in;
        bit xfer_ok;

        if (transfer == null) return;
        if (transfer.xfer_type !=
                svt_usb_transfer::CONTROL_TRANSFER) return;
        if (transfer.setup_data_bmrequesttype_type !=
                svt_usb_types::CLASS) return;
        if (transfer.setup_data_bmrequesttype_recipient !=
                svt_usb_types::BMREQ_INTERFACE) return;
        if (transfer.setup_data_brequest != OCP_BREQUEST_XFER) return;

        cmd_code = transfer.setup_data_w_value[7:0];
        dir_in = transfer.setup_data_bmrequesttype_dir ==
                 svt_usb_types::DEVICE_TO_HOST;
        xfer_ok = is_xfer_successful(transfer);
        if (!xfer_ok) total_nonsuccess_xfers++;
        total_class_xfers++;
        if (!xfer_count.exists(cmd_code)) begin
            xfer_count[cmd_code][0] = 0;
            xfer_count[cmd_code][1] = 0;
        end
        xfer_count[cmd_code][dir_in ? 1 : 0]++;

        `uvm_info_context("OCPREC_MARK",
            $sformatf("OCPREC_XFER cmd=0x%02h dir=%s wIndex=0x%04h wLength=%0d status=%s",
                      cmd_code, dir_in ? "IN" : "OUT",
                      transfer.setup_data_w_index,
                      transfer.setup_data_w_length,
                      xfer_ok ? "SUCCESSFUL" : "NON_SUCCESS"),
            UVM_NONE, this)

        case (cmd_code)
            OCP_CMD_PROT_CAP: begin
                if (dir_in && xfer_ok) begin
                    int start_index;
                    int end_index;
                    total_prot_cap_in++;
                    if (!valid_payload_window(
                            transfer, start_index, end_index) ||
                        ((end_index - start_index) < 8)) begin
                        `uvm_error("OCPREC_MARK",
                            "PROT_CAP IN payload is shorter than its magic string.")
                        total_prot_cap_mismatch++;
                    end else begin
                        for (int unsigned i = 0; i < 8; i++) begin
                            if (transfer.payload.data[start_index + i] !==
                                    OCP_SPEC_PROT_CAP_MAGIC[i]) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("PROT_CAP magic byte %0d expected 0x%02h got 0x%02h.",
                                              i,
                                              OCP_SPEC_PROT_CAP_MAGIC[i],
                                              transfer.payload.data[
                                                  start_index + i]))
                                total_prot_cap_mismatch++;
                            end
                        end
                    end
                end
            end

            OCP_CMD_INDIRECT_FIFO_CTRL: begin
                if (!dir_in &&
                    caliptra_ss_usb_out_payload_complete(transfer) &&
                    (transfer.setup_data_w_length >=
                        OCP_SPEC_LEN_INDIRECT_FIFO_CTRL) &&
                    (transfer.payload.data[OCP_OFF_IFC_RESET] == 8'h01)) begin
                    reset_fifo_model();
                    `uvm_info("OCPREC_MARK",
                        "INDIRECT_FIFO_CTRL RESET established an empty FIFO model baseline.",
                        UVM_NONE)
                end
            end

            OCP_CMD_INDIRECT_FIFO_DATA: begin
                if (!dir_in) begin
                    if (caliptra_ss_usb_out_payload_complete(transfer))
                        queue_fifo_write_attempt(transfer);
                end else if (xfer_ok &&
                             (region_type ==
                                OCP_REGION_RECOVERY_CODE_WO)) begin
                    check_fifo_data_read(transfer);
                end
            end

            OCP_CMD_INDIRECT_FIFO_STATUS: begin
                if (dir_in && xfer_ok) check_fifo_status(transfer);
            end

            default: ;
        endcase
    endfunction

    function void report_phase(uvm_phase phase);
        bit [7:0] cmd;
        string line;
        int unsigned issued;
        super.report_phase(phase);

        line = "";
        if (xfer_count.first(cmd)) begin
            do begin
                line = {line,
                    $sformatf(" cmd=0x%02h OUT=%0d IN=%0d;",
                              cmd, xfer_count[cmd][0],
                              xfer_count[cmd][1])};
            end while (xfer_count.next(cmd));
        end

        if (uvm_config_db#(int unsigned)::get(
                null, "", "ocp_transfers_issued", issued) &&
            (issued != total_class_xfers)) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("OCPREC transfer-count mismatch: sequence issued=%0d scoreboard observed=%0d.",
                          issued, total_class_xfers))
        end

        `uvm_info_context("OCPREC_MARK",
            $sformatf("OCPREC_SUMMARY total=%0d nonsuccess=%0d prot_cap_in=%0d prot_cap_mismatch=%0d fifo_data_out_bytes=%0d fifo_data_in=%0d fifo_external_reads=%0d fifo_status_in=%0d fifo_rejected_dwords=%0d fifo_size=%0d max_transfer_dwords=%0d model_bytes=%0d%s",
                      total_class_xfers, total_nonsuccess_xfers,
                      total_prot_cap_in, total_prot_cap_mismatch,
                      total_fifo_data_out_bytes, total_fifo_data_in,
                      total_fifo_external_reads,
                      total_fifo_status_in, total_fifo_rejected_dwords,
                      fifo_size, max_transfer_dwords,
                      committed_fifo_bytes.size(), line),
            UVM_NONE, this)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_SCOREBOARD_SV
