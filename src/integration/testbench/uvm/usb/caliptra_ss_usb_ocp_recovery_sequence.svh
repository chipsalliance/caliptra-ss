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

`ifndef CALIPTRA_SS_USB_OCP_RECOVERY_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_RECOVERY_SEQUENCE_SV

// =============================================================================
// caliptra_ss_usb_ocp_recovery_sequence
//
// EP0-only OCP Recovery v1.1 class-transfer choreography. Composes the
// existing caliptra_ss_usb_init_sequence (to reach Configured state per
// USB 2.0 sec 9.1.1.5), then issues OCP Recovery class-spec CONTROL
// transfers (OCP Recovery v1.1 sec 8.5.1) on the same host_agent
// virt_sequencer. Every command is exactly one EP0 control transfer:
// no bulk endpoints are used (sec 8.5).
//
// Per OCP Recovery v1.1 sec 8.5.1, the setup-stage encoding is fixed:
//   bmRequestType[6:5] = 01b (Class)
//   bmRequestType[4:0] = 00001b (Interface)
//   bRequest           = 0x00 (OCP_RECOVERY_TRANSFER)
//   wValue[7:0]        = OCP Recovery command code (0x22..0x2F)
//   wValue[15:8]       = 0
//   wIndex[7:0]        = bInterfaceNumber of the recovery interface
//   wIndex[15:8]       = 0
//   wLength            = byte count of the data stage. For Read direction,
//                        sec 8.5.1 mandates wLength == wMaxRdTransferSize
//                        (stricter than USB 2.0 sec 9.3.5 which allows
//                        short-packet termination). For Write direction,
//                        wLength <= wMaxWrTransferSize.
//
// wMaxRdTransferSize / wMaxWrTransferSize are read from the
// OCP_RECOVERY_FUNCTIONAL descriptor (bDescriptorType=0x24,
// bDescriptorSubType=0x01) inside the configuration descriptor blob
// returned by GET_DESCRIPTOR(CONFIGURATION) per OCP Recovery v1.1 sec
// 8.5.3.
// =============================================================================

// OCP Recovery v1.1 sec 9.2: Command Codes. Spec assigns codes
// 0x22..0x2F to the OCP recovery commands; values outside that range are
// reserved.
typedef enum bit [7:0] {
    OCP_REC_CMD_PROT_CAP            = 8'h22, // sec 9.2 (Read)
    OCP_REC_CMD_DEVICE_ID           = 8'h23, // sec 9.2 (Read)
    OCP_REC_CMD_DEVICE_STATUS       = 8'h24, // sec 9.2 (Read)
    OCP_REC_CMD_RESET               = 8'h25, // sec 9.2 (Write)
    OCP_REC_CMD_RECOVERY_CTRL       = 8'h26, // sec 9.2 (R/W)
    OCP_REC_CMD_RECOVERY_STATUS     = 8'h27, // sec 9.2 (Read)
    OCP_REC_CMD_HW_STATUS           = 8'h28, // sec 9.2 (Read)
    OCP_REC_CMD_INDIRECT_CTRL       = 8'h29, // sec 9.2 cmd 41 (R/W)
    OCP_REC_CMD_INDIRECT_STATUS     = 8'h2A, // sec 9.2 cmd 42 (Read)
    OCP_REC_CMD_INDIRECT_DATA       = 8'h2B, // sec 9.2 cmd 43 (R/W)
    OCP_REC_CMD_VENDOR              = 8'h2C, // sec 9.2 cmd 44 (R/W)
    OCP_REC_CMD_INDIRECT_FIFO_CTRL  = 8'h2D, // sec 9.2 cmd 45 (R/W)
    OCP_REC_CMD_INDIRECT_FIFO_STATUS= 8'h2E, // sec 9.2 cmd 46 (Read)
    OCP_REC_CMD_INDIRECT_FIFO_DATA  = 8'h2F  // sec 9.2 cmd 47 (Write)
} caliptra_ss_usb_ocp_recovery_cmd_e;

// OCP Recovery v1.1 sec 9.2 PROT_CAP Magic String: ASCII "OCP RECV".
// Single source of truth for both the stimulus sequence and the scoreboard
// PROT_CAP check (eliminates the duplicate literal flagged by review m2).
localparam bit [7:0] OCP_PROT_CAP_MAGIC [8] = '{
    8'h4F, 8'h43, 8'h50, 8'h20,  // 'O' 'C' 'P' ' '
    8'h52, 8'h45, 8'h43, 8'h56}; // 'R' 'E' 'C' 'V'

// OCP Recovery v1.1 Sec 9.2 PROT_CAP bytes 10-11 (Recovery Protocol Capabilities).
// FIFO-only push-image recovery: bit5 (direct CMS-memory window) cleared, bit11 (flashless boot)
// set (R4). 0x169B base | 0x0800 (bit11) = 0x1E9B. Matches the RDL PROT_CAP_2.AGENT_CAPS reset.
localparam bit [15:0] OCP_PROT_CAP_AGENT_CAPS_EXP = 16'h1E9B;

// OCP Recovery v1.1 Sec 9.2 PROT_CAP bytes 8-9 (Recovery protocol version):
// byte 8 = major = 0x01, byte 9 = minor = 0x01 -> little-endian 16-bit 0x0101. Matches the RDL
// PROT_CAP_2.REC_PROT_VERSION reset.
localparam bit [15:0] OCP_PROT_CAP_VERSION_EXP = 16'h0101;

// OCP Recovery v1.1 sec 8.5.3 bcdOCPRecVersion: BCD encoding of the spec
// revision. v1.1 = 0x0110.
localparam bit [15:0] OCP_REC_BCD_VERSION_V1P1 = 16'h0110;

class caliptra_ss_usb_ocp_recovery_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_recovery_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    // Resolved once at top of body() via resolve_xfer_handles().
    protected svt_usb_agent         host_agent_h;
    protected svt_usb_configuration usb_cfg;
    protected svt_usb_status        shared_status;

    // Parsed from OCP_RECOVERY_FUNCTIONAL descriptor (sec 8.5.3).
    // Defaults are spec-allowed minimums; if descriptor parse fails the
    // sequence falls back to 64 (USB 2.0 HS EP0 wMaxPacketSize) so smoke
    // probes can still run.
    protected int unsigned wMaxRdTransferSize = 64;
    protected int unsigned wMaxWrTransferSize = 64;
    protected bit [15:0]   bcdOCPRecVersion   = 16'h0110;
    protected bit          func_desc_found    = 1'b0;

    // Selected device address (1 after enumeration).
    protected int dev_addr_v = 1;

    // Review M6: count of OCP *class* transfers we issue. Published via
    // uvm_config_db at end of body() so the scoreboard's report_phase can
    // cross-check against the count observed on the analysis port.
    // Per-sample uvm_event drops on back-to-back triggers are otherwise
    // silent; this counter makes that loss observable.
    //
    // M6 follow-up (count-domain fix): this counter MUST stay in the same
    // observation domain as the scoreboard, which filters its analysis-port
    // stream down to CLASS / BMREQ_INTERFACE / bRequest==0x00 transfers
    // (caliptra_ss_usb_ocp_scoreboard.svh write() lines 116-120). It is
    // therefore incremented ONLY in ocp_class_xfer() below. The two STANDARD
    // GET_DESCRIPTOR(CONFIGURATION) reads in body() are forwarded by the env
    // but correctly dropped by the scoreboard's class filter, so they MUST
    // NOT be counted here -- counting them produced the prior false
    // "issued=11 observed=9" cross-check failure (the two standard descriptor
    // reads, not a dropped NOTIFY_USB_TRANSFER_ENDED sample).
    protected int unsigned transfers_issued = 0;

    function new(string name = "caliptra_ss_usb_ocp_recovery_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Helper: issue a single OCP Recovery class-spec EP0 control transfer.
    //
    //   dir_in   : 1 = IN (DEVICE_TO_HOST, Read direction per sec 8.5.1)
    //              0 = OUT (HOST_TO_DEVICE, Write direction)
    //   cmd_code : OCP Recovery command (sec 9.2)
    //   wlength  : data-stage byte count. Caller is responsible for setting
    //              wlength == wMaxRdTransferSize on IN (sec 8.5.1) and
    //              wlength <= wMaxWrTransferSize on OUT.
    //   payload_bytes : for OUT, raw bytes to drive on the data stage;
    //                   ignored for IN.
    //   resp_bytes    : for IN, populated from the completed transfer's
    //                   payload.data[]; left empty on OUT.
    //   label    : used as a uvm_info anchor and as the transfer name.
    //
    // Pattern: extends do_control_xfer choreography by inlining start_item /
    // randomize / finish_item so we can pin the OUT payload.data[] inside the
    // randomize() with{} constraint (the VIP packetizes the OUT data stage
    // from payload.data during randomize; constraining it is the supported way
    // to drive deterministic OUT bytes -- see usb_vip_ocp_recovery_class_xfers.md
    // sec 1 and bug_usb_ocp_out_payload_not_driven_tb).
    // -------------------------------------------------------------------------
    protected virtual task ocp_class_xfer(
        input  bit              dir_in,
        input  bit [7:0]        cmd_code,
        input  bit [15:0]       wlength,
        ref    bit [7:0]        payload_bytes[$],
        ref    bit [7:0]        resp_bytes[$],
        input  string           label);

        svt_usb_transfer req;
        bit [7:0]        bm_dir;
        bit [15:0]       wvalue_v;
        bit [15:0]       windex_v;
        int              n;

        bm_dir   = dir_in ? svt_usb_types::DEVICE_TO_HOST
                          : svt_usb_types::HOST_TO_DEVICE;
        wvalue_v = {8'h00, cmd_code};
        // wIndex: low byte = bInterfaceNumber, high byte = 0 per sec 8.5.1.
        windex_v = 16'h0000;
        windex_v[7:0] = 8'(get_iface_num());

        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);

        if (usb_cfg != null) req.cfg = usb_cfg;
        req.fix_anchors(0, 0, 0);

        // For OUT (HOST_TO_DEVICE) class transfers, the data stage bytes must
        // be made deterministic on the wire. Construct the svt_usb_payload and
        // size its data array BEFORE randomize() so the VIP has a non-null
        // payload handle to solve against, then PIN payload.data inside the
        // randomize() with{} block below. The VIP generates/packetizes the OUT
        // data stage from payload.data during randomize (post_randomize); a
        // post-randomize poke of payload.data[] is therefore too late and was
        // overwritten by the VIP's randomized payload (the host transmitted
        // random bytes on the wire). See bug_usb_ocp_out_payload_not_driven_tb.
        n = payload_bytes.size();
        if (!dir_in) begin
            req.payload = svt_usb_payload::type_id::create("payload");
            if (req.payload == null) begin
                `uvm_fatal("OCPREC",
                    $sformatf("svt_usb_payload::type_id::create returned null for %s (cmd=0x%02h)",
                              label, cmd_code))
            end
            req.payload.data = new[n];
        end

        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == dev_addr_v;
                setup_data_bmrequesttype_dir       == bm_dir;
                setup_data_bmrequesttype_type      == svt_usb_types::CLASS;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_INTERFACE;
                setup_data_brequest                == 8'h00;             // OCP_RECOVERY_TRANSFER sec 8.5.1
                setup_data_w_value                 == wvalue_v;
                setup_data_w_index                 == windex_v;
                setup_data_w_length                == wlength;
                payload_intended_byte_count        == wlength;
                // Pin the OUT data-stage bytes so the VIP transmits exactly
                // payload_bytes (in order) instead of a randomized payload.
                // For IN this block is skipped (payload.data is filled by the
                // VIP from the device response and must stay unconstrained).
                if (!dir_in) {
                    payload.data.size() == n;
                    foreach (payload.data[i]) payload.data[i] == payload_bytes[i];
                }
            }) begin
            `uvm_fatal("OCPREC",
                $sformatf("svt_usb_transfer randomize() failed for %s (cmd=0x%02h)",
                          label, cmd_code))
        end

        finish_item(req, -1);

        // Track issued transfers for the scoreboard cross-check (review M6).
        transfers_issued++;

        // Block until the host stack has completed the bus transaction so
        // we can mine the IN payload (and so the next transfer is properly
        // ordered).
        host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();

        if (dir_in) begin
            resp_bytes.delete();
            // VIP returns the device-side bytes in req.payload.data[].
            // Copy up to wlength bytes (some commands return short; we
            // copy whatever the VIP populated, capped at wlength).
            // Review M2: payload may legally be null on a stalled IN.
            if (req.payload == null) begin
                `uvm_info("OCPREC",
                    $sformatf("IN xfer %s (cmd=0x%02h) returned null payload; resp_bytes left empty.",
                              label, cmd_code),
                    UVM_LOW)
            end else begin
                for (int i = 0; i < wlength; i++) begin
                    resp_bytes.push_back(req.payload.data[i]);
                end
            end
        end

        // Anchor info bound to this sequence (UVM_NONE so it survives
        // +svt_debug_opts rerouting only if the sequence's report-object
        // is not a VIP component path -- see usb_vip_ocp_recovery sec 6.
        // The corresponding scoreboard emits an OCPREC_MARK line from a
        // non-VIP path which is the canonical log-scrape anchor).
        `uvm_info("OCPREC",
            $sformatf("OCP xfer %s cmd=0x%02h dir=%s wLength=%0d",
                      label, cmd_code, dir_in ? "IN" : "OUT", wlength),
            UVM_NONE)
    endtask

    // -------------------------------------------------------------------------
    // Helper: parse the OCP_RECOVERY_FUNCTIONAL descriptor from a configuration
    // descriptor blob. Walks the standard USB 2.0 descriptor TLV stream
    // (each entry: bLength @ off0, bDescriptorType @ off1, then bLength-2
    // payload bytes) and looks for the entry with bDescriptorType=0x24
    // (Class-Specific Interface, OCP Recovery v1.1 sec 8.5.3) and
    // bDescriptorSubType=0x01.
    //
    // Layout (OCP Recovery v1.1 sec 8.5.3 Tbl OCP_RECOVERY_FUNCTIONAL):
    //   off 0 : bLength (== 9)
    //   off 1 : bDescriptorType (0x24)
    //   off 2 : bDescriptorSubType (0x01)
    //   off 3 : bcdOCPRecVersion[7:0]
    //   off 4 : bcdOCPRecVersion[15:8]
    //   off 5 : wMaxRdTransferSize[7:0]
    //   off 6 : wMaxRdTransferSize[15:8]
    //   off 7 : wMaxWrTransferSize[7:0]
    //   off 8 : wMaxWrTransferSize[15:8]
    // -------------------------------------------------------------------------
    protected virtual function void parse_functional_descriptor(ref bit [7:0] blob[$]);
        int idx;
        int blen;
        idx = 0;
        func_desc_found = 1'b0;
        while (idx + 2 <= blob.size()) begin
            blen = blob[idx];
            if (blen < 2) break;                      // malformed, abort walk
            if (idx + blen > blob.size()) break;      // truncated entry
            if (blob[idx+1] == 8'h24) begin
                // Class-specific interface descriptor; check subtype 0x01.
                if (blen >= 9 && blob[idx+2] == 8'h01) begin
                    bcdOCPRecVersion[7:0]   = blob[idx+3];
                    bcdOCPRecVersion[15:8]  = blob[idx+4];
                    wMaxRdTransferSize      = {blob[idx+6], blob[idx+5]};
                    wMaxWrTransferSize      = {blob[idx+8], blob[idx+7]};
                    func_desc_found         = 1'b1;
                    return;
                end
            end
            idx += blen;
        end
    endfunction

    // Convenience: returns the interface number to address. Reads from the
    // shared_cfg if available; defaults to 0 (OCP Recovery v1.1 sec 8.5.2
    // RECOMMENDED 00h).
    protected virtual function int get_iface_num();
        caliptra_ss_usb_shared_cfg scfg;
        uvm_component              parent_comp;
        // Best-effort: try to find a caliptra_ss_usb_shared_cfg from the
        // test's resource scope. Fall back to 0 if not visible.
        if (uvm_config_db#(caliptra_ss_usb_shared_cfg)::get(null, "",
                "cfg", scfg)) begin
            return scfg.ocp_recovery_iface_num;
        end
        return 0;
    endfunction

    // -------------------------------------------------------------------------
    // body(): full OCP Recovery EP0 choreography
    // -------------------------------------------------------------------------
    virtual task body();
        caliptra_ss_usb_init_sequence init_seq;
        bit [7:0] empty_q[$];
        bit [7:0] resp_q[$];
        bit [7:0] cfg_blob[$];
        bit [7:0] prot_cap[$];
        bit [7:0] dev_id[$];
        bit [7:0] dev_status[$];
        bit [7:0] rec_status[$];
        bit [7:0] recovery_ctrl_payload[$];
        bit [7:0] indir_fifo_ctrl_payload[$];
        bit [7:0] image_chunk[$];
        bit [7:0] fifo_status[$];
        int      poll_iter;
        bit      recovery_pending_seen;
        int      n_dwords;
        bit [31:0] pattern_dw[$];
        int       i;

        // 1. Resolve VIP handles for our own xfers.
        resolve_xfer_handles(host_agent_h, usb_cfg, shared_status);

        `uvm_info("OCPREC",
            "Starting caliptra_ss_usb_init_sequence to reach Configured state.",
            UVM_NONE)

        // 2. Compose: run the init sequence to drive the bus to Configured.
        //    Per usb_vip_ocp_recovery_class_xfers.md sec 5, the recovery
        //    sequence must wait for SET_CONFIGURATION to complete (OCP
        //    Recovery v1.1 sec 8.5: "MUST respond ... once USB enumeration
        //    is complete and USB Device has entered the configured state").
        init_seq = caliptra_ss_usb_init_sequence::type_id::create("init_seq");
        init_seq.start(p_sequencer, this);

        `uvm_info("OCPREC",
            "Init sequence completed; device is Configured. Starting OCP probe.",
            UVM_NONE)

        // 3. Parse the OCP_RECOVERY_FUNCTIONAL descriptor (sec 8.5.3) from
        //    GET_DESCRIPTOR(CONFIGURATION). Review M1: USB 2.0 sec 9.4.3
        //    requires a two-stage read because wTotalLength is not known
        //    a-priori. A single 255-byte fetch with
        //    payload_intended_byte_count==255 tells the VIP to wait for
        //    255 bytes; the IP-3511 device terminates early with a short
        //    packet, manifesting as a NAK/timeout, and the unbounded copy
        //    loop reads X past the actual payload, possibly tricking the
        //    descriptor walker into a spurious 0x24 type hit.
        //    Stage 1: fetch the 9-byte Configuration Descriptor header to
        //    decode wTotalLength (bytes 2-3, little-endian).
        //    Stage 2: re-issue with wLength == wTotalLength.
        begin
            svt_usb_transfer creq;
            int unsigned     w_total_length;
            int unsigned     copy_len;
            bit [7:0]        hdr_blob[$];

            creq = svt_usb_transfer::type_id::create("OCPREC_GET_CONFIG_DESC_HDR_req");
            start_item(creq, -1, p_sequencer.xfer_sequencer);
            if (usb_cfg != null) creq.cfg = usb_cfg;
            creq.fix_anchors(0, 0, 0);
            if (!creq.randomize() with {
                    xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                    device_address                     == dev_addr_v;
                    setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
                    setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
                    setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
                    setup_data_brequest                == 8'h06;          // GET_DESCRIPTOR
                    setup_data_w_value                 == 16'h0200;       // CONFIGURATION
                    setup_data_w_index                 == 16'h0000;
                    setup_data_w_length                == 16'h0009;       // header only
                }) begin
                `uvm_fatal("OCPREC", "randomize failed for OCPREC_GET_CONFIG_DESC_HDR")
            end
            finish_item(creq, -1);
            // Count-domain fix (M6): do NOT increment transfers_issued here.
            // This is a STANDARD GET_DESCRIPTOR(CONFIGURATION) read which the
            // scoreboard's class filter drops, so counting it would desync the
            // issued-vs-observed cross-check. transfers_issued tracks CLASS
            // transfers only (see decl comment + ocp_class_xfer()).
            host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();

            hdr_blob.delete();
            if (creq.payload == null) begin
                `uvm_error("OCPREC",
                    "Stage-1 GET_DESCRIPTOR(CONFIGURATION,wLength=9) returned null payload; falling back to defaults.")
                w_total_length = 0;
            end else begin
                for (int j = 0; j < 9; j++) hdr_blob.push_back(creq.payload.data[j]);
                // wTotalLength: bytes 2-3 little-endian (USB 2.0 Tbl 9-10).
                w_total_length = {hdr_blob[3], hdr_blob[2]};
                `uvm_info("OCPREC",
                    $sformatf("Stage-1 CONFIGURATION header parsed: wTotalLength=%0d.",
                              w_total_length),
                    UVM_NONE)
            end

            cfg_blob.delete();
            if (w_total_length < 9) begin
                `uvm_error("OCPREC",
                    $sformatf("Stage-1 wTotalLength=%0d is impossibly short (< 9 byte header).",
                              w_total_length))
            end else begin
                svt_usb_transfer creq2;
                creq2 = svt_usb_transfer::type_id::create("OCPREC_GET_CONFIG_DESC_FULL_req");
                start_item(creq2, -1, p_sequencer.xfer_sequencer);
                if (usb_cfg != null) creq2.cfg = usb_cfg;
                creq2.fix_anchors(0, 0, 0);
                if (!creq2.randomize() with {
                        xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                        device_address                     == dev_addr_v;
                        setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
                        setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
                        setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
                        setup_data_brequest                == 8'h06;     // GET_DESCRIPTOR
                        setup_data_w_value                 == 16'h0200;  // CONFIGURATION
                        setup_data_w_index                 == 16'h0000;
                        setup_data_w_length                == 16'(w_total_length);
                    }) begin
                    `uvm_fatal("OCPREC", "randomize failed for OCPREC_GET_CONFIG_DESC_FULL")
                end
                finish_item(creq2, -1);
                // Count-domain fix (M6): STANDARD descriptor read; not counted
                // (see the Stage-1 read above and the transfers_issued decl).
                host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();

                if (creq2.payload == null) begin
                    `uvm_error("OCPREC",
                        "Stage-2 GET_DESCRIPTOR(CONFIGURATION) returned null payload.")
                end else begin
                    // Bound the push loop by the actual wTotalLength
                    // (review M1) so the walker sees only valid bytes.
                    copy_len = w_total_length;
                    for (int j = 0; j < copy_len; j++)
                        cfg_blob.push_back(creq2.payload.data[j]);
                    `uvm_info("OCPREC",
                        $sformatf("Stage-2 GET_DESCRIPTOR(CONFIGURATION) completed; %0d bytes copied; parsing for OCP_RECOVERY_FUNCTIONAL.",
                                  cfg_blob.size()),
                        UVM_NONE)
                end
            end
        end

        parse_functional_descriptor(cfg_blob);
        if (!func_desc_found) begin
            `uvm_info("OCPREC",
                "OCP_RECOVERY_FUNCTIONAL descriptor (type 0x24/0x01) not found in CONFIGURATION blob. Using default wMaxRdTransferSize=wMaxWrTransferSize=64.",
                UVM_NONE)
        end else begin
            `uvm_info("OCPREC",
                $sformatf("OCP_RECOVERY_FUNCTIONAL parsed: bcdOCPRecVersion=0x%04h wMaxRdTransferSize=%0d wMaxWrTransferSize=%0d",
                          bcdOCPRecVersion, wMaxRdTransferSize, wMaxWrTransferSize),
                UVM_NONE)
            // Review m6: validate against expected OCP Recovery v1.1
            // encoding (sec 8.5.3). BCD high byte = major, low byte = minor.
            if (bcdOCPRecVersion[15:8] != OCP_REC_BCD_VERSION_V1P1[15:8]) begin
                `uvm_error("OCPREC",
                    $sformatf("bcdOCPRecVersion major mismatch: got=0x%04h expected=0x%04h (OCP Recovery v1.1 sec 8.5.3).",
                              bcdOCPRecVersion, OCP_REC_BCD_VERSION_V1P1))
            end else if (bcdOCPRecVersion[7:0] != OCP_REC_BCD_VERSION_V1P1[7:0]) begin
                `uvm_warning("OCPREC",
                    $sformatf("bcdOCPRecVersion minor differs: got=0x%04h expected=0x%04h (OCP Recovery v1.1 sec 8.5.3).",
                              bcdOCPRecVersion, OCP_REC_BCD_VERSION_V1P1))
            end
        end

        // Per OCP Recovery v1.1 sec 8.5.1, wMaxRdTransferSize MUST be >= 64.
        if (wMaxRdTransferSize < 64) begin
            `uvm_error("OCPREC",
                $sformatf("wMaxRdTransferSize=%0d violates OCP Recovery v1.1 sec 8.5.1 minimum of 64 bytes.",
                          wMaxRdTransferSize))
            wMaxRdTransferSize = 64;
        end

        // ---------------------------------------------------------------------
        // 4. Probe (smoke) phase
        // ---------------------------------------------------------------------

        // 4a. PROT_CAP IN: first 8 bytes ASCII "OCP RECV"
        //     (sec 9.2 row "Magic String").
        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_PROT_CAP),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(prot_cap),
                       .label("OCPREC_PROT_CAP"));
        // PROT_CAP magic per OCP Recovery v1.1 sec 9.2 (review m2:
        // shared OCP_PROT_CAP_MAGIC localparam used by both seq and sb).
        if (prot_cap.size() < 8) begin
            `uvm_error("OCPREC",
                $sformatf("PROT_CAP returned only %0d bytes; expected >= 8 for magic string.",
                          prot_cap.size()))
        end else begin
            for (int j = 0; j < 8; j++) begin
                if (prot_cap[j] !== OCP_PROT_CAP_MAGIC[j]) begin
                    `uvm_error("OCPREC",
                        $sformatf("PROT_CAP magic byte %0d mismatch: exp=0x%02h got=0x%02h",
                                  j, OCP_PROT_CAP_MAGIC[j], prot_cap[j]))
                end
            end
        end

        // PROT_CAP version + AGENT_CAPS read-back (sec 9.2). The magic
        // loop above maps PROT_CAP byte k -> prot_cap[k] (e.g. byte 0 = 'O' = 0x4F),
        // so version is bytes 8-9 (major/minor) and AGENT_CAPS is bytes 10-11
        // (LSB = byte 10, MSB = byte 11); assemble each little-endian.
        if (prot_cap.size() < 12) begin
            `uvm_error("OCPREC",
                $sformatf("PROT_CAP returned only %0d bytes; expected >= 12 for version (8-9) and AGENT_CAPS (10-11).",
                          prot_cap.size()))
        end else begin
            logic [15:0] agent_caps;
            logic [15:0] prot_version;
            prot_version = {prot_cap[9], prot_cap[8]};
            if (prot_version !== OCP_PROT_CAP_VERSION_EXP) begin
                `uvm_error("OCPREC",
                    $sformatf("PROT_CAP version mismatch: got=0x%04h exp=0x%04h (OCP Recovery v1.1 Sec 9.2 bytes 8-9: major=0x01, minor=0x01).",
                              prot_version, OCP_PROT_CAP_VERSION_EXP))
            end
            agent_caps = {prot_cap[11], prot_cap[10]};
            if (agent_caps !== OCP_PROT_CAP_AGENT_CAPS_EXP) begin
                `uvm_error("OCPREC",
                    $sformatf("PROT_CAP AGENT_CAPS mismatch: got=0x%04h exp=0x%04h (OCP Recovery v1.1 Sec 9.2 bytes 10-11; FIFO-only bit5=0, flashless bit11=1).",
                              agent_caps, OCP_PROT_CAP_AGENT_CAPS_EXP))
            end
        end

        // 4b. DEVICE_ID IN.
        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_ID),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(dev_id),
                       .label("OCPREC_DEVICE_ID"));
        `uvm_info("OCPREC",
            $sformatf("DEVICE_ID returned %0d bytes; first 4: 0x%02h 0x%02h 0x%02h 0x%02h",
                      dev_id.size(),
                      dev_id.size() > 0 ? dev_id[0] : 8'h00,
                      dev_id.size() > 1 ? dev_id[1] : 8'h00,
                      dev_id.size() > 2 ? dev_id[2] : 8'h00,
                      dev_id.size() > 3 ? dev_id[3] : 8'h00),
            UVM_NONE)

        // 4c. DEVICE_STATUS IN. byte[0] is Device Status code;
        //     sec 9.2 defines 0x00 = Status Pending, 0x01 = Device
        //     Healthy. Other values are also legal but logged for visibility.
        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(dev_status),
                       .label("OCPREC_DEVICE_STATUS"));
        if (dev_status.size() < 1) begin
            `uvm_error("OCPREC",
                "DEVICE_STATUS returned 0 bytes; expected at least 1 (Device Status).")
        end else begin
            `uvm_info("OCPREC",
                $sformatf("DEVICE_STATUS[0]=0x%02h (sec 9.2 reason code).",
                          dev_status[0]),
                UVM_NONE)
        end

        // 4d. RECOVERY_STATUS IN.
        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_RECOVERY_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(rec_status),
                       .label("OCPREC_RECOVERY_STATUS"));
        if (rec_status.size() < 1) begin
            `uvm_error("OCPREC",
                "RECOVERY_STATUS returned 0 bytes; expected at least 1 (sec 9.2).")
        end else begin
            `uvm_info("OCPREC",
                $sformatf("RECOVERY_STATUS[0]=0x%02h (sec 9.2).",
                          rec_status[0]),
                UVM_NONE)
        end

        // ---------------------------------------------------------------------
        // V2: Unsupported-command PROTOCOL_ERROR negative check (R4 / OCP
        //     Recovery v1.1 Sec 9.1: "an unsupported command MUST set an
        //     unsupported error condition in the DEVICE_STATUS"; Sec 9.2 Tbl
        //     9-6 byte 1 = 0x01 "Unsupported/Write Command", clear-on-read).
        //     INDIRECT_CTRL is the direct CMS-memory window, which
        //     this FIFO-only transport does not implement (removed in R3; not
        //     advertised: AGENT_CAPS bit5 = 0).  The device STALLs the request
        //     (a legal "unsupported" response; the control pipe auto-clears the
        //     stall on the next SETUP per USB 2.0 sec 8.5.3.4) and latches
        //     PROTOCOL_ERROR = 0x01.
        //     Done here -- before the recovery flow (section 5) -- so the
        //     Caliptra-core firmware is not yet polling DEVICE_STATUS (each such
        //     read would clear PROTOCOL_ERROR before this check observes it).
        // ---------------------------------------------------------------------
        begin
            bit [7:0] unsup_resp[$];
            bit [7:0] ds_proto[$];
            bit [7:0] ds_proto_clr[$];

            // Issue the unsupported command.  The IN read is expected to STALL;
            // a null/short response payload is tolerated and not checked.
            empty_q.delete();
            unsup_resp.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_INDIRECT_CTRL),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(unsup_resp),
                           .label("OCPREC_UNSUPPORTED_INDIRECT_CTRL"));

            // First DEVICE_STATUS read: PROTOCOL_ERROR (byte 1) must be 0x01.
            // This read also clears it (onread = rclr).
            empty_q.delete();
            ds_proto.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(ds_proto),
                           .label("OCPREC_DEVICE_STATUS_PROTOERR"));
            if (ds_proto.size() < 2) begin
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS after unsupported command returned %0d bytes; need >= 2 to read PROTOCOL_ERROR (byte 1).",
                              ds_proto.size()))
            end else if (ds_proto[1] !== 8'h01) begin
                `uvm_error("OCPREC",
                    $sformatf("PROTOCOL_ERROR not set after unsupported command 0x29: DEVICE_STATUS[1]=0x%02h, expected 0x01 (OCP Recovery v1.1 Sec 9.1 / Sec 9.2).",
                              ds_proto[1]))
            end else begin
                `uvm_info("OCPREC",
                    "V2: PROTOCOL_ERROR=0x01 correctly set after unsupported command 0x29 (OCP Recovery v1.1 Sec 9.1).",
                    UVM_NONE)
            end

            // Second DEVICE_STATUS read: PROTOCOL_ERROR must now read 0x00
            // (clear-on-read semantic).
            empty_q.delete();
            ds_proto_clr.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(ds_proto_clr),
                           .label("OCPREC_DEVICE_STATUS_PROTOERR_CLR"));
            if (ds_proto_clr.size() < 2) begin
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS (clear check) returned %0d bytes; need >= 2.",
                              ds_proto_clr.size()))
            end else if (ds_proto_clr[1] !== 8'h00) begin
                `uvm_error("OCPREC",
                    $sformatf("PROTOCOL_ERROR did not clear on read: DEVICE_STATUS[1]=0x%02h, expected 0x00 (OCP Recovery v1.1 Sec 9.1 clear-on-read).",
                              ds_proto_clr[1]))
            end else begin
                `uvm_info("OCPREC",
                    "V2: PROTOCOL_ERROR cleared to 0x00 on DEVICE_STATUS read (clear-on-read).",
                    UVM_NONE)
            end
        end

        // ---------------------------------------------------------------------
        // 5. Streaming-boot-lite phase
        // ---------------------------------------------------------------------

        // 5pre. RECOVERY_CTRL OUT: initiate recovery so the device
        //     recovery FSM leaves S_IDLE. The RTL FSM
        //     (third_party/usb2/src/integration/rtl/usb_ocp_recovery_fsm.sv,
        //     S_IDLE lines 224-246) only advances on a RECOVERY_CTRL byte-0
        //     (CMS) write strobe (recovery_ctrl_wr_cms). Without this write the
        //     FSM stays in S_IDLE, the INDIRECT_FIFO image push below is
        //     ignored, and DEVICE_STATUS never reports 0x04 RECOVERY_PENDING.
        //     FSM path: S_IDLE --(recovery_ctrl_wr_cms)--> S_DETECTED
        //               --> S_AWAIT_IMAGE --(image_push_active)--> S_PUSH_ACTIVE
        //               --(image_push_done)--> S_IMAGE_LOADED (=DS_RECOVERY_PENDING).
        //     Payload per OCP Recovery v1.1 Section 9.2 (RECOVERY_CTRL):
        //       byte 0 : Component Memory Space (CMS) index -> 0 (select CMS 0)
        //       byte 1 : Recovery Image Selection           -> 0 (use stored/
        //                                                         streamed image)
        //       byte 2 : Activate Recovery Image            -> 0 (do NOT activate
        //                                                         yet; activation
        //                                                         is a later step,
        //                                                         RECOVERY_CTRL activate = 0x0F)
        //     wLength = 3: a partial-word (non-word-multiple) OUT that also
        //     exercises the partial-word OUT coverage required by the plan.
        recovery_ctrl_payload = '{8'h00, 8'h00, 8'h00};
        `uvm_info("OCPREC",
            "RECOVERY_CTRL (cmd 0x26) OUT: CMS=0, ImgSel=0, Activate=0 (sec 9.2). Initiating recovery to advance FSM out of S_IDLE.",
            UVM_NONE)
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_RECOVERY_CTRL),
                       .wlength(16'(recovery_ctrl_payload.size())),
                       .payload_bytes(recovery_ctrl_payload),
                       .resp_bytes(resp_q),
                       .label("OCPREC_RECOVERY_CTRL"));

        // 5a. INDIRECT_FIFO_CTRL OUT: select CMS index 0,
        //     reset FIFO, set IMAGE_SIZE to 12 (4-byte units; sec 9.2
        //     INDIRECT_FIFO_CTRL IMAGE_SIZE unit = 4 bytes => 12 * 4 = 48 bytes).
        //     The image size is deliberately NOT equal to the firmware's
        //     scratch-buffer constant so the device-programmed size must be
        //     read back correctly (it exercises the INDIRECT_FIFO_CTRL
        //     IMAGE_SIZE byte placement, OCP Recovery v1.1 Sec 9.2:
        //     IMAGE_SIZE occupies bytes 2..5, straddling CTRL_0/CTRL_1).
        //     Per OCP Recovery v1.1 Section 8.2.5, FIFO CMS uses ONLY
        //     INDIRECT_FIFO_* family; INDIRECT_CTRL is mutually exclusive
        //     (Memory Window CMS) and must NOT be touched in this path.
        //     Layout per INDIRECT_FIFO_CTRL (Sec 9.2):
        //       byte 0     : CMS index            -> 0
        //       byte 1     : Reset (1 = reset)    -> 1
        //       bytes 2..5 : IMAGE_SIZE (4B units, LE) -> 12
        indir_fifo_ctrl_payload = '{8'h00, 8'h01,
                                    8'h0C, 8'h00, 8'h00, 8'h00};
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_CTRL),
                       .wlength(16'(indir_fifo_ctrl_payload.size())),
                       .payload_bytes(indir_fifo_ctrl_payload),
                       .resp_bytes(resp_q),
                       .label("OCPREC_INDIRECT_FIFO_CTRL"));

        // 5b. INDIRECT_FIFO_DATA OUT: push 48 bytes (12 dwords)
        //     of synthetic image with a recognizable pattern so the
        //     scoreboard can match (OCP Recovery v1.1 sec 9.2: cmd 0x2F
        //     is the streaming write to the FIFO). wLength must be
        //     <= wMaxWrTransferSize per sec 8.5.1. The count matches the
        //     programmed IMAGE_SIZE above.
        n_dwords = 12;
        pattern_dw.delete();
        pattern_dw.push_back(32'hDEADBEEF);
        pattern_dw.push_back(32'hCAFEBABE);
        pattern_dw.push_back(32'h12345678);
        pattern_dw.push_back(32'h9ABCDEF0);
        // Fill remainder with incrementing dwords starting at 0x0000_0010.
        for (int j = pattern_dw.size(); j < n_dwords; j++)
            pattern_dw.push_back(32'h00000010 + j);

        image_chunk.delete();
        for (int j = 0; j < n_dwords; j++) begin
            // LE byte order.
            image_chunk.push_back(pattern_dw[j][ 7: 0]);
            image_chunk.push_back(pattern_dw[j][15: 8]);
            image_chunk.push_back(pattern_dw[j][23:16]);
            image_chunk.push_back(pattern_dw[j][31:24]);
        end
        if (image_chunk.size() > wMaxWrTransferSize) begin
            `uvm_error("OCPREC",
                $sformatf("Image chunk size %0d > wMaxWrTransferSize %0d (sec 8.5.1).",
                          image_chunk.size(), wMaxWrTransferSize))
        end
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_DATA),
                       .wlength(16'(image_chunk.size())),
                       .payload_bytes(image_chunk),
                       .resp_bytes(resp_q),
                       .label("OCPREC_INDIRECT_FIFO_DATA"));

        // 5c. INDIRECT_FIFO_STATUS IN: expect WRITE_INDEX
        //     advanced by n_dwords (4-byte units). Per sec 9.2:
        //       byte 0       : EMPTY (1=empty)
        //       byte 1       : FULL
        //       byte 2       : REGION
        //       byte 3       : Reserved
        //       bytes 4..7   : WRITE_INDEX (4-byte units, LE)
        //       bytes 8..11  : READ_INDEX  (4-byte units, LE)
        //       bytes 12..15 : FIFO_SIZE   (4-byte units, LE)
        //       bytes 16..19 : MAX_TRANSFER_SIZE (bytes, LE)
        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(fifo_status),
                       .label("OCPREC_INDIRECT_FIFO_STATUS"));
        if (fifo_status.size() >= 8) begin
            int unsigned wr_idx;
            wr_idx = {fifo_status[7], fifo_status[6],
                      fifo_status[5], fifo_status[4]};
            `uvm_info("OCPREC",
                $sformatf("INDIRECT_FIFO_STATUS: EMPTY=%0d FULL=%0d WRITE_INDEX=%0d (4B units; expected %0d)",
                          fifo_status[0], fifo_status[1], wr_idx, n_dwords),
                UVM_NONE)
            if (wr_idx != n_dwords) begin
                `uvm_error("OCPREC",
                    $sformatf("INDIRECT_FIFO_STATUS.WRITE_INDEX=%0d, expected %0d after pushing %0d dwords (sec 9.2).",
                              wr_idx, n_dwords, n_dwords))
            end
        end else begin
            `uvm_error("OCPREC",
                $sformatf("INDIRECT_FIFO_STATUS returned %0d bytes; need >= 8 to extract WRITE_INDEX (sec 9.2).",
                          fifo_status.size()))
        end

        // 5d. Poll DEVICE_STATUS until firmware advances past
        //     the awaiting-image phase. Per OCP Recovery v1.1 Sec 9.2
        //     DEVICE_STATUS byte 0 holds "Device Status"; the FSM raises it
        //     to 0x04 RECOVERY_PENDING on S_IMAGE_LOADED, while
        //     RECOVERY_STATUS byte 0 stays at 0x01 Awaiting Image until
        //     activation. Polling DEVICE_STATUS therefore observes the
        //     correct image-loaded transition. Bounded iterations so the
        //     test fails closed if firmware never advances.
        poll_iter = 0;
        recovery_pending_seen = 1'b0;
        forever begin
            empty_q.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(dev_status),
                           .label($sformatf("OCPREC_DEVICE_STATUS_poll%0d", poll_iter)));
            if (dev_status.size() < 1) begin
                `uvm_error("OCPREC",
                    "DEVICE_STATUS poll returned 0 bytes.")
                break;
            end
            `uvm_info("OCPREC",
                $sformatf("Polling DEVICE_STATUS[0]=0x%02h iter=%0d (sec 9.2).",
                          dev_status[0], poll_iter),
                UVM_NONE)
            // Exit on RECOVERY_PENDING (0x04) per sec 9.2: the
            // device has loaded a recovery image and is ready for the
            // activation step (RECOVERY_CTRL.activate=0x0F, Sec 9.2).
            if (dev_status[0] == 8'h04) begin
                recovery_pending_seen = 1'b1;
                break;
            end
            poll_iter++;
            if (poll_iter > 16) begin
                // Review M3: fail closed. The block comment above states
                // the intent is to fail closed if firmware never
                // advances, so this exit path MUST raise an error
                // (uvm_info would be re-routed by +svt_debug_opts and
                // the timeout would slip).
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS did not reach 0x04 RECOVERY_PENDING within 16 polls. last dev_status[0]=0x%02h time=%0t",
                              dev_status.size() > 0 ? dev_status[0] : 8'h00,
                              $time))
                break;
            end
            #50us;
        end

        // End-of-test handshake (Problem 1 fix).
        //
        // Observing DEVICE_STATUS==0x04 RECOVERY_PENDING only means the device
        // FSM has loaded the recovery image; the streaming-boot is NOT yet
        // complete. Caliptra still has to drain the INDIRECT_FIFO, write
        // RECOVERY_CTRL.activate, and assert SS_GENERIC_FW_EXEC_CTRL_0[2]
        // (observed ~40 us after 0x04), after which the MCU firmware reports
        // the result by writing TB_CMD_END_SIM_WITH_SUCCESS to its TB mailbox.
        // That mailbox write is what truly ends the simulation: the TB services
        // block (caliptra_ss_top_tb_services.sv) calls $finish on it,
        // pre-empting everything else.
        //
        // Previously, body() returned the instant 0x04 was seen. That dropped
        // the main_phase default-sequence objection and let uvm_root $finish
        // the sim ~93 ns AFTER FW_EXEC_CTRL asserted -- before the MCU could
        // observe it and report the pass. The MCU handoff was lost.
        //
        // Fix: once RECOVERY_PENDING is seen, keep body() (and therefore the
        // main_phase objection) alive so the MCU can complete the streaming
        // boot and drive its pass. The real terminal event is the MCU's
        // TB_CMD_END_SIM_WITH_SUCCESS $finish, which interrupts the wait below
        // the moment it occurs -- so on a passing run this wait ends early via
        // that external $finish. The bound is a fail-safe only: it is large
        // enough to cover the observed drain->activate->signal->MCU-pass
        // latency (~40 us) with ample margin, yet well under the UVM test
        // timeout, so a firmware that never finishes still terminates the
        // sequence (with whatever errors were logged) rather than hanging
        // unbounded.
        if (recovery_pending_seen) begin
            `uvm_info("OCPREC",
                "DEVICE_STATUS=0x04 RECOVERY_PENDING observed. Holding the main_phase objection so the MCU can complete streaming-boot and report TB_CMD_END_SIM_WITH_SUCCESS (which $finishes the sim). Bounded fail-safe wait engaged.",
                UVM_NONE)
            // Bounded keep-alive. The MCU's TB_CMD_END_SIM_WITH_SUCCESS $finish
            // normally ends the sim long before this elapses.
            #200us;
            `uvm_warning("OCPREC",
                "Bounded post-RECOVERY_PENDING keep-alive (200us) elapsed without the MCU ending the sim via TB_CMD_END_SIM_WITH_SUCCESS. The streaming-boot handoff did not complete; ending the sequence so the test can report.")
        end

        // Review M6: publish the issued transfer count so the scoreboard's
        // report_phase can cross-check against transfers observed on the
        // analysis port. A drift indicates that NOTIFY_USB_TRANSFER_ENDED
        // back-to-back triggers were dropped at the env forwarder, which
        // would otherwise be silent.
        uvm_config_db#(int unsigned)::set(null, "*",
            "ocp_transfers_issued", transfers_issued);

        `uvm_info("OCPREC", "OCP recovery sequence complete", UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_RECOVERY_SEQUENCE_SV
