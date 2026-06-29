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
//     equal ASCII "OCP RECV" (sec 9.2 Tbl 9-3 "Magic String").
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

    // ASCII "OCP RECV" (OCP Recovery v1.1 sec 9.2 Tbl 9-3 PROT_CAP magic).
    // Review m2: reference the shared OCP_PROT_CAP_MAGIC localparam from
    // caliptra_ss_usb_ocp_recovery_sequence.svh (same package scope) instead
    // of redeclaring the byte array here.

    // Accumulated INDIRECT_FIFO_DATA bytes (OUT direction). The scoreboard
    // compares these against the FIFO state reported by
    // INDIRECT_FIFO_STATUS (IN direction).
    protected bit [7:0]   pushed_fifo_bytes[$];

    // Per-cmd, per-direction counters: [cmd_code][0=OUT, 1=IN].
    protected int unsigned xfer_count[bit[7:0]][2];
    protected int unsigned total_class_xfers;
    protected int unsigned total_prot_cap_in;
    protected int unsigned total_prot_cap_mismatch;
    protected int unsigned total_fifo_data_out_bytes;
    protected int unsigned total_fifo_status_in;
    // Review M7: count transfers that arrived with a non-success status so
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
        total_fifo_status_in        = 0;
        total_nonsuccess_xfers      = 0;
    endfunction

    // Review M7: returns 1 if the transfer completed successfully on the
    // bus, 0 otherwise (NAK / STALL / TIMEOUT / etc.). Synopsys USB VIP
    // does NOT expose a "SUCCESSFUL" enum. Per UVM Class Reference for
    // svt_usb_transfer, the canonical success predicate is
    // `results_status == '0` (each bit flags a specific failure mode;
    // OR of all bits is 0 on a clean transfer). The inherited `status`
    // member is the svt_sequence_item processing-state enum (INITIAL/
    // ACTIVE/ACCEPT/ABORTED/...), only used here to rule out ABORTED.
    // Centralized so a future VIP version-bump that renames either
    // field can be patched in one place.
    protected virtual function bit is_xfer_successful(svt_usb_transfer t);
        if (t == null) return 0;
        return (t.results_status == '0) &&
               (t.status != svt_sequence_item::ABORTED);
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
        // Review M7: include the transfer status so operator can correlate
        // a skipped accumulation back to a NAK/STALL on the bus.
        `uvm_info_context("OCPREC_MARK",
            $sformatf("OCPREC_XFER cmd=0x%02h dir=%s wIndex=0x%04h wLength=%0d status=%s",
                      cmd_code, dir_in ? "IN" : "OUT",
                      t.setup_data_w_index, t.setup_data_w_length,
                      xfer_ok ? "SUCCESSFUL" : "NON_SUCCESS"),
            UVM_NONE, this)

        // Per-command predicates. Review m3: cast to the OCP cmd enum so
        // the case arms use spec-named symbols instead of raw 8'h22/etc.
        case (caliptra_ss_usb_ocp_recovery_cmd_e'(cmd_code))

            // PROT_CAP (sec 9.2 Tbl 9-3): IN responses must begin with the
            // 8-byte ASCII magic "OCP RECV".
            OCP_REC_CMD_PROT_CAP: begin
                if (dir_in) begin
                    if (!xfer_ok) begin
                        `uvm_info("OCPREC_MARK",
                            "PROT_CAP IN skipped: transfer status NON_SUCCESS (review M7).",
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
                    if (!xfer_ok) begin
                        `uvm_info("OCPREC_MARK",
                            "INDIRECT_FIFO_DATA OUT skipped: transfer status NON_SUCCESS; bytes NOT accumulated into pushed_fifo_bytes (review M7).",
                            UVM_NONE)
                    end else if (t.payload == null) begin
                        `uvm_error("OCPREC_MARK",
                            "INDIRECT_FIFO_DATA OUT observed with null payload.")
                    end else begin
                        for (int i = 0; i < t.setup_data_w_length; i++) begin
                            pushed_fifo_bytes.push_back(t.payload.data[i]);
                        end
                        total_fifo_data_out_bytes += t.setup_data_w_length;
                    end
                end
            end

            // INDIRECT_FIFO_STATUS (sec 9.2 Tbl 9-15): byte[0]=EMPTY,
            // byte[1]=FULL, bytes[4..7]=WRITE_INDEX (4-byte units).
            OCP_REC_CMD_INDIRECT_FIFO_STATUS: begin
                if (dir_in) begin
                    if (!xfer_ok) begin
                        `uvm_info("OCPREC_MARK",
                            "INDIRECT_FIFO_STATUS IN skipped: transfer status NON_SUCCESS; WRITE_INDEX comparison suppressed (review M7).",
                            UVM_NONE)
                    end else begin
                        total_fifo_status_in++;
                        if (t.payload == null) begin
                            `uvm_error("OCPREC_MARK",
                                "INDIRECT_FIFO_STATUS IN observed with null payload.")
                        end else begin
                            int unsigned wr_idx;
                            int unsigned expected_dwords;
                            wr_idx = {t.payload.data[7], t.payload.data[6],
                                      t.payload.data[5], t.payload.data[4]};
                            expected_dwords = pushed_fifo_bytes.size() / 4;
                            if (wr_idx != expected_dwords) begin
                                `uvm_error("OCPREC_MARK",
                                    $sformatf("INDIRECT_FIFO_STATUS.WRITE_INDEX=%0d (4B units); scoreboard expected %0d (from %0d pushed bytes). Mismatch at dword index %0d (sec 9.2 Tbl 9-15).",
                                              wr_idx, expected_dwords,
                                              pushed_fifo_bytes.size(),
                                              expected_dwords < wr_idx ? expected_dwords : wr_idx))
                            end
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

        // Review M6: cross-check observed CLASS transfers against the count
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
                    $sformatf("OCPREC transfer-count mismatch: sequence issued=%0d, scoreboard observed=%0d. Likely a dropped NOTIFY_USB_TRANSFER_ENDED sample (review M6).",
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
            $sformatf("OCPREC_SUMMARY total=%0d nonsuccess=%0d prot_cap_in=%0d prot_cap_mismatch=%0d fifo_data_out_bytes=%0d fifo_status_in=%0d%s",
                      total_class_xfers, total_nonsuccess_xfers,
                      total_prot_cap_in,
                      total_prot_cap_mismatch, total_fifo_data_out_bytes,
                      total_fifo_status_in, line),
            UVM_NONE, this)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_SCOREBOARD_SV
