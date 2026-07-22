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

// =============================================================================
// caliptra_ss_usb_ocp_scoreboard
//
// Passive checker for OCP Recovery v1.1 EP0 class-specific control
// transfers. Subscribes to the host-side completed-transfer stream and
// applies the predicates below:
//
//   * Filter: only CONTROL_TRANSFER items with bmRequestType.type==CLASS,
//     bmRequestType.recipient==BMREQ_INTERFACE, and bRequest==0x00 (OCP
//     Recovery v1.1 sec 8.5.1 OCP_RECOVERY_TRANSFER).
//   * For every filtered transfer, emit one OCPREC_MARK info line in the
//     exact format
//        OCPREC_XFER cmd=0x%02h dir=%s wIndex=0x%04h wLength=%0d
//     bound via `uvm_info_context to this component (non-VIP path) so it
//     survives +svt_debug_opts rerouting per
//     usb_vip_ocp_recovery_class_xfers.md sec 6.
//   * For PROT_CAP IN responses: first 8 payload bytes must
//     equal ASCII "OCP RECV" (sec 9.2 "Magic String").
//   * For INDIRECT_FIFO_DATA OUT requests: the data-stage
//     payload is captured into expected_fifo_data. On the next
//     INDIRECT_FIFO_STATUS IN read, WRITE_INDEX (bytes 4..7,
//     in 4-byte units) is compared against the total dwords previously
//     pushed -- mismatch raises UVM_ERROR with the offending dword index.
//   * Per-command, per-direction observation counters are maintained
//     and emitted as a UVM_NONE summary line in report_phase.
// =============================================================================
class caliptra_ss_usb_ocp_scoreboard extends uvm_component;

    `uvm_component_utils(caliptra_ss_usb_ocp_scoreboard)

    uvm_analysis_imp #(svt_usb_transfer, caliptra_ss_usb_ocp_scoreboard)
        transfer_imp;

    // ASCII "OCP RECV" (OCP Recovery v1.1 sec 9.2 PROT_CAP magic).
    // References the shared OCP_PROT_CAP_MAGIC localparam from
    // caliptra_ss_usb_ocp_recovery_sequence.svh (same package scope) instead
    // of redeclaring the byte array here.

    // Spec model for the INDIRECT_FIFO ring (OCP Recovery v1.1 Sec 8.2.5).
    // The queue stores accepted DWORD payload bytes in FIFO order, while the
    // indices and occupancy track the externally visible modulo-65 ring.
    protected bit [7:0]   expected_fifo_bytes[$];
    protected int unsigned expected_write_index;
    protected int unsigned expected_actual_occupancy;
    protected int unsigned expected_visible_occupancy;

    // Per-cmd, per-direction counters: [cmd_code][0=OUT, 1=IN].
    protected int unsigned xfer_count[bit[7:0]][2];
    protected int unsigned total_class_xfers;
    protected int unsigned total_prot_cap_in;
    protected int unsigned total_prot_cap_mismatch;
    protected int unsigned total_fifo_data_out_bytes;
    protected int unsigned total_fifo_data_in;
    protected int unsigned total_fifo_status_in;
    // Count transfers that arrived with a non-success status so
    // they can be reported and skipped from PROT_CAP / FIFO accounting.
    protected int unsigned total_nonsuccess_xfers;

    function new(string name = "caliptra_ss_usb_ocp_scoreboard",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        transfer_imp = new("transfer_imp", this);
        total_class_xfers           = 0;
        total_prot_cap_in           = 0;
        total_prot_cap_mismatch     = 0;
        total_fifo_data_out_bytes   = 0;
        total_fifo_data_in          = 0;
        total_fifo_status_in        = 0;
        total_nonsuccess_xfers      = 0;
        expected_write_index        = 0;
        expected_actual_occupancy   = 0;
        expected_visible_occupancy  = 0;
    endfunction

    // Returns 1 if the transfer completed successfully on the bus, 0 otherwise
    // (NAK / STALL / TIMEOUT / etc.). In this SVT USB VIP revision, OUT control
    // transfers retire with status==ACCEPT even when results_status carries a
    // non-zero bookkeeping bit, while IN transfers report a clean completion
    // through results_status=='0'. Use the direction-specific predicate so the
    // scoreboard models accepted FIFO writes and still treats failed IN reads as
    // non-success.
    protected virtual function bit is_xfer_successful(svt_usb_transfer t);
        if (t == null) return 0;
        if (t.setup_data_bmrequesttype_dir == svt_usb_types::HOST_TO_DEVICE) begin
            return (t.status == svt_sequence_item::ACCEPT);
        end
        return (t.results_status == '0) &&
               (t.status != svt_sequence_item::ABORTED);
    endfunction

    // The VIP can classify an OUT control transfer as non-success after it has
    // delivered the complete DATA stage. FIFO state is changed by that DATA
    // stage, so model it whenever the observed payload is complete and the
    // transfer was not aborted.
    protected virtual function bit has_complete_out_payload(svt_usb_transfer t);
        if (t == null) return 0;
        if (t.setup_data_bmrequesttype_dir != svt_usb_types::HOST_TO_DEVICE) return 0;
        if (t.status == svt_sequence_item::ABORTED) return 0;
        if (t.payload == null) return 0;
        return (t.payload.data.size() >= t.setup_data_w_length);
    endfunction

    protected virtual function int unsigned fifo_ring_next(int unsigned idx);
        return (idx == usb_ocp_recovery_pkg::OCP_FIFO_INDEX_MAX) ? 0 : (idx + 1);
    endfunction

    protected virtual function void reset_fifo_model();
        expected_fifo_bytes.delete();
        expected_write_index = 0;
        expected_actual_occupancy  = 0;
        expected_visible_occupancy = 0;
    endfunction

    protected virtual function void model_fifo_push(svt_usb_transfer t);
        int word_count;
        int byte_idx;
        if (t.payload == null) return;
        if ((t.setup_data_w_length % 4) != 0) begin
            `uvm_warning("OCPREC_MARK",
                $sformatf("INDIRECT_FIFO_DATA OUT length %0d is not DWORD aligned; scoreboard models only full DWORD pushes.",
                          t.setup_data_w_length))
        end
        word_count = t.setup_data_w_length / 4;
        for (int word = 0; word < word_count; word++) begin
            if (expected_visible_occupancy < usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS) begin
                byte_idx = word * 4;
                expected_fifo_bytes.push_back(t.payload.data[byte_idx + 0]);
                expected_fifo_bytes.push_back(t.payload.data[byte_idx + 1]);
                expected_fifo_bytes.push_back(t.payload.data[byte_idx + 2]);
                expected_fifo_bytes.push_back(t.payload.data[byte_idx + 3]);
                expected_write_index = fifo_ring_next(expected_write_index);
                expected_actual_occupancy++;
                expected_visible_occupancy++;
            end
        end
        total_fifo_data_out_bytes += t.setup_data_w_length;
    endfunction

    protected virtual function void model_fifo_pop_and_check(svt_usb_transfer t);
        bit [7:0] exp_byte;
        if (t.payload == null) begin
            `uvm_error("OCPREC_MARK",
                "INDIRECT_FIFO_DATA IN observed with null payload.")
            return;
        end
        if (t.payload.data.size() < 4) begin
            `uvm_error("OCPREC_MARK",
                $sformatf("INDIRECT_FIFO_DATA IN payload too short: %0d bytes, need >= 4.",
                          t.payload.data.size()))
            return;
        end
        total_fifo_data_in++;
        if (expected_fifo_bytes.size() < 4) begin
            `uvm_error("OCPREC_MARK",
                "INDIRECT_FIFO_DATA IN observed while scoreboard expected FIFO empty.")
            return;
        end
        for (int i = 0; i < 4; i++) begin
            exp_byte = expected_fifo_bytes.pop_front();
            if (t.payload.data[i] !== exp_byte) begin
                `uvm_error("OCPREC_MARK",
                    $sformatf("INDIRECT_FIFO_DATA byte %0d mismatch: exp=0x%02h got=0x%02h.",
                              i, exp_byte, t.payload.data[i]))
            end
        end
        expected_actual_occupancy--;
    endfunction

    // -------------------------------------------------------------------------
    // write(): analysis-imp callback.
    // -------------------------------------------------------------------------
    virtual function void write(svt_usb_transfer t);
        bit [7:0] cmd_code;
        bit       dir_in;
        bit [7:0] dir_raw;
        bit       xfer_ok;

        if (t == null) return;

        // Filter: CONTROL_TRANSFER + CLASS + BMREQ_INTERFACE + bRequest==0x00.
        if (t.xfer_type != svt_usb_transfer::CONTROL_TRANSFER) return;
        if (t.setup_data_bmrequesttype_type      != svt_usb_types::CLASS) return;
        if (t.setup_data_bmrequesttype_recipient != svt_usb_types::BMREQ_INTERFACE)
            return;
        if (t.setup_data_brequest != 8'h00) return;

        cmd_code = t.setup_data_w_value[7:0];
        dir_raw  = t.setup_data_bmrequesttype_dir;
        dir_in   = (dir_raw == svt_usb_types::DEVICE_TO_HOST);
        xfer_ok  = is_xfer_successful(t);
        if (!xfer_ok) total_nonsuccess_xfers++;

        total_class_xfers++;
        if (!xfer_count.exists(cmd_code)) begin
            xfer_count[cmd_code][0] = 0;
            xfer_count[cmd_code][1] = 0;
        end
        xfer_count[cmd_code][dir_in ? 1 : 0]++;

        // Anchor marker (UVM_NONE, _context to *this* non-VIP component).
        // Includes the transfer status so the operator can correlate
        // a skipped accumulation back to a NAK/STALL on the bus.
        `uvm_info_context("OCPREC_MARK",
            $sformatf("OCPREC_XFER cmd=0x%02h dir=%s wIndex=0x%04h wLength=%0d status=%s",
                      cmd_code, dir_in ? "IN" : "OUT",
                      t.setup_data_w_index, t.setup_data_w_length,
                      xfer_ok ? "SUCCESSFUL" : "NON_SUCCESS"),
            UVM_NONE, this)

        // Per-command predicates. Cast to the OCP cmd enum so
        // the case arms use spec-named symbols instead of raw 8'h22/etc.
        case (caliptra_ss_usb_ocp_recovery_cmd_e'(cmd_code))

            // PROT_CAP (sec 9.2): IN responses must begin with the
            // 8-byte ASCII magic "OCP RECV".
            OCP_REC_CMD_PROT_CAP: begin
                if (dir_in) begin
                    if (!xfer_ok) begin
                        `uvm_info("OCPREC_MARK",
                            "PROT_CAP IN skipped: transfer status NON_SUCCESS.",
                            UVM_NONE)
                    end else begin
                        total_prot_cap_in++;
                        if (t.payload == null) begin
                            `uvm_error("OCPREC_MARK",
                                "PROT_CAP IN observed with null payload.")
                            total_prot_cap_mismatch++;
                        end else begin
                            bit mismatch;
                            mismatch = 1'b0;
                            for (int i = 0; i < 8; i++) begin
                                if (t.payload.data[i] !== OCP_PROT_CAP_MAGIC[i]) begin
                                    `uvm_error("OCPREC_MARK",
                                        $sformatf("PROT_CAP magic mismatch at byte %0d: exp=0x%02h got=0x%02h",
                                                  i, OCP_PROT_CAP_MAGIC[i],
                                                  t.payload.data[i]))
                                    mismatch = 1'b1;
                                end
                            end
                            if (mismatch) total_prot_cap_mismatch++;
                        end
                    end
                end
            end

            // INDIRECT_FIFO_DATA (sec 9.2): OUT data-stage bytes are
            // appended to the expected-push log. The next FIFO_STATUS IN
            // is checked against this log.
            OCP_REC_CMD_INDIRECT_FIFO_DATA: begin
                if (!dir_in) begin
                    if (!has_complete_out_payload(t)) begin
                        `uvm_info("OCPREC_MARK",
                            "INDIRECT_FIFO_DATA OUT skipped: DATA payload was incomplete or aborted.",
                            UVM_NONE)
                    end else begin
                        model_fifo_push(t);
                    end
                end else if (!xfer_ok) begin
                    `uvm_info("OCPREC_MARK",
                        "INDIRECT_FIFO_DATA IN skipped: transfer status NON_SUCCESS; pop-order comparison suppressed.",
                        UVM_NONE)
                end else begin
                    model_fifo_pop_and_check(t);
                end
            end

            // INDIRECT_FIFO_CTRL writes with Reset=1 clear the protocol ring and
            // payload store (OCP Recovery v1.1 Sec 9.2 INDIRECT_FIFO_CTRL).
            OCP_REC_CMD_INDIRECT_FIFO_CTRL: begin
                if (!dir_in && has_complete_out_payload(t) &&
                    (t.setup_data_w_length >= 2) && t.payload.data[1][0]) begin
                    reset_fifo_model();
                end
            end

            // INDIRECT_FIFO_STATUS (sec 9.2): byte[0]=EMPTY, byte[1]=FULL,
            // bytes[4..7]=WRITE_INDEX, bytes[8..11]=READ_INDEX, bytes[12..15]
            // = FIFO_SIZE, bytes[16..19] = MAX_TRANSFER_SIZE.
            OCP_REC_CMD_INDIRECT_FIFO_STATUS: begin
                if (dir_in) begin
                    if (!xfer_ok) begin
                        `uvm_info("OCPREC_MARK",
                            "INDIRECT_FIFO_STATUS IN skipped: transfer status NON_SUCCESS; FIFO ring comparison suppressed.",
                            UVM_NONE)
                    end else begin
                        total_fifo_status_in++;
                        if (t.payload == null) begin
                            `uvm_error("OCPREC_MARK",
                                "INDIRECT_FIFO_STATUS IN observed with null payload.")
                        end else if (t.payload.data.size() < 20) begin
                            `uvm_error("OCPREC_MARK",
                                $sformatf("INDIRECT_FIFO_STATUS payload too short: %0d bytes, need >= 20.",
                                          t.payload.data.size()))
                        end else begin
                            int unsigned wr_idx;
                            int unsigned rd_idx;
                            int unsigned visible_occupancy;
                            int unsigned fifo_size;
                            int unsigned max_transfer;
                            bit got_empty;
                            bit got_full;
                            wr_idx = {t.payload.data[7], t.payload.data[6],
                                      t.payload.data[5], t.payload.data[4]};
                            rd_idx = {t.payload.data[11], t.payload.data[10],
                                      t.payload.data[9], t.payload.data[8]};
                            fifo_size = {t.payload.data[15], t.payload.data[14],
                                         t.payload.data[13], t.payload.data[12]};
                            max_transfer = {t.payload.data[19], t.payload.data[18],
                                            t.payload.data[17], t.payload.data[16]};
                            got_empty = t.payload.data[0][0];
                            got_full  = t.payload.data[0][1];
                            visible_occupancy = (wr_idx >= rd_idx) ?
                                (wr_idx - rd_idx) :
                                (wr_idx + usb_ocp_recovery_pkg::OCP_FIFO_RING_SIZE_DWORDS - rd_idx);
                            if (visible_occupancy < expected_actual_occupancy ||
                                visible_occupancy > expected_visible_occupancy) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("INDIRECT_FIFO_STATUS visible occupancy=%0d outside conservative range [%0d,%0d].",
                                              visible_occupancy, expected_actual_occupancy, expected_visible_occupancy))
                            end
                            if (got_empty !== (visible_occupancy == 0)) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("INDIRECT_FIFO_STATUS.EMPTY=%0d, expected %0d.",
                                              got_empty, visible_occupancy == 0))
                            end
                            if (got_full !== (visible_occupancy == usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS)) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("INDIRECT_FIFO_STATUS.FULL=%0d, expected %0d.",
                                              got_full,
                                              visible_occupancy == usb_ocp_recovery_pkg::OCP_FIFO_PHYSICAL_DEPTH_DWORDS))
                            end
                            if (wr_idx != expected_write_index) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("INDIRECT_FIFO_STATUS.WRITE_INDEX=%0d, expected %0d.",
                                              wr_idx, expected_write_index))
                            end
                            if (fifo_size != usb_ocp_recovery_pkg::OCP_FIFO_RING_SIZE_DWORDS) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("INDIRECT_FIFO_STATUS.FIFO_SIZE=%0d, expected %0d.",
                                              fifo_size, usb_ocp_recovery_pkg::OCP_FIFO_RING_SIZE_DWORDS))
                            end
                            if (max_transfer != usb_ocp_recovery_pkg::OCP_FIFO_MAX_TRANSFER_DWORDS) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("INDIRECT_FIFO_STATUS.MAX_TRANSFER_SIZE=%0d, expected %0d.",
                                              max_transfer, usb_ocp_recovery_pkg::OCP_FIFO_MAX_TRANSFER_DWORDS))
                            end
                            expected_visible_occupancy = visible_occupancy;
                        end
                    end
                end
            end

            default: ; // no per-cmd predicate; counted above.
        endcase
    endfunction

    // -------------------------------------------------------------------------
    // report_phase: summary line for log scraping.
    // -------------------------------------------------------------------------
    function void report_phase(uvm_phase phase);
        bit [7:0]      cmd;
        string         line;
        int unsigned   issued;
        super.report_phase(phase);

        line = "";
        if (xfer_count.first(cmd)) begin
            do begin
                line = {line,
                    $sformatf(" cmd=0x%02h OUT=%0d IN=%0d;",
                              cmd, xfer_count[cmd][0], xfer_count[cmd][1])};
            end while (xfer_count.next(cmd));
        end

        // Cross-check observed CLASS transfers against the count
        // the sequence reports having issued. Both counters now live in the
        // same CLASS-transfer domain: the sequence increments transfers_issued
        // only in ocp_class_xfer() (NOT for the two STANDARD
        // GET_DESCRIPTOR(CONFIGURATION) reads, which this scoreboard's filter
        // at write() drops). A residual drift therefore genuinely indicates a
        // missed NOTIFY_USB_TRANSFER_ENDED trigger sample in the env forwarder.
        if (uvm_config_db#(int unsigned)::get(null, "",
                "ocp_transfers_issued", issued)) begin
            if (issued != total_class_xfers) begin
                `uvm_error("OCPREC_MARK",
                    $sformatf("OCPREC transfer-count mismatch: sequence issued=%0d, scoreboard observed=%0d. Likely a dropped NOTIFY_USB_TRANSFER_ENDED sample.",
                              issued, total_class_xfers))
            end else begin
                `uvm_info_context("OCPREC_MARK",
                    $sformatf("OCPREC transfer-count cross-check OK: issued=%0d observed=%0d.",
                              issued, total_class_xfers),
                    UVM_NONE, this)
            end
        end else begin
            `uvm_info_context("OCPREC_MARK",
                "OCPREC transfer-count cross-check skipped: ocp_transfers_issued not published (sequence did not run, or pre-M6 sequence).",
                UVM_NONE, this)
        end

        `uvm_info_context("OCPREC_MARK",
            $sformatf("OCPREC_SUMMARY total=%0d nonsuccess=%0d prot_cap_in=%0d prot_cap_mismatch=%0d fifo_data_out_bytes=%0d fifo_data_in=%0d fifo_status_in=%0d%s",
                      total_class_xfers, total_nonsuccess_xfers,
                      total_prot_cap_in,
                      total_prot_cap_mismatch, total_fifo_data_out_bytes,
                      total_fifo_data_in, total_fifo_status_in, line),
            UVM_NONE, this)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_SCOREBOARD_SV
