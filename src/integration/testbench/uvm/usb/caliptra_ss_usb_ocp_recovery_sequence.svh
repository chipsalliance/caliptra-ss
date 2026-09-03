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

class caliptra_ss_usb_ocp_recovery_sequence
    extends caliptra_ss_usb_ocp_recovery_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_recovery_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected virtual caliptra_ss_usb_ocp_access_semantics_if sem_vif;

    function new(string name = "caliptra_ss_usb_ocp_recovery_sequence");
        super.new(name);
    endfunction

    protected virtual function bit get_sem_vif();
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
                    null, "uvm_test_top.env",
                    "ocp_access_semantics_if", sem_vif)) begin
            `uvm_fatal("OCP_FW_STATUS",
                "ocp_access_semantics_if not found in config_db")
            return 1'b0;
        end
        return 1'b1;
    endfunction

    protected virtual task wait_firmware_ready_status();
        bit [7:0] device_status[$];
        bit [7:0] recovery_status[$];
        bit       reached;

        reached = 1'b0;
        for (int unsigned poll = 0; poll < 20; poll++) begin
            ocp_read(
                OCP_REC_CMD_DEVICE_STATUS,
                device_status,
                $sformatf("OCP_FW_DEVICE_STATUS_READY_%0d", poll));
            ocp_read(
                OCP_REC_CMD_RECOVERY_STATUS,
                recovery_status,
                $sformatf("OCP_FW_RECOVERY_STATUS_READY_%0d", poll));

            if ((device_status.size() > OCP_OFF_DS_VENDOR_LEN) &&
                (recovery_status.size() >= OCP_SPEC_LEN_RECOVERY_STATUS) &&
                (device_status[OCP_OFF_DS_STATUS] ===
                    OCP_DEVICE_STATUS_RECOVERY_MODE) &&
                (device_status[OCP_OFF_DS_PROT_ERROR] ===
                    OCP_PROTOCOL_ERROR_NONE) &&
                (recovery_status[
                    OCP_OFF_RS_STATUS_IMAGE_INDEX][3:0] ===
                    OCP_RECOVERY_STATUS_AWAITING_IMAGE) &&
                (recovery_status[
                    OCP_OFF_RS_STATUS_IMAGE_INDEX][7:4] === 4'h0) &&
                (recovery_status[OCP_OFF_RS_VENDOR_STATUS] === 8'h00)) begin
                reached = 1'b1;
                break;
            end
            #5us;
        end

        if (!reached) begin
            `uvm_error("OCP_FW_STATUS",
                "Firmware did not publish Recovery Mode/Awaiting Image status within the bounded interval.")
        end else begin
            `uvm_info("OCP_FW_STATUS",
                "Firmware-published Recovery Mode/Awaiting Image status observed through USB.",
                UVM_NONE)
        end
    endtask

    // -------------------------------------------------------------------------
    // body(): full OCP Recovery EP0 choreography
    // -------------------------------------------------------------------------
    virtual task body();
        bit [7:0] empty_q[$];
        bit [7:0] resp_q[$];
        bit [7:0] prot_cap[$];
        bit [7:0] dev_id[$];
        bit [7:0] dev_status[$];
        bit [7:0] rec_status[$];
        bit [7:0] recovery_ctrl_payload[$];
        bit [7:0] indir_fifo_ctrl_payload[$];
        bit [7:0] image_chunk[$];
        bit [7:0] fifo_status[$];
        bit [7:0] prot_cap_wr_payload[$];
        int      poll_iter;
        bit      recovery_pending_seen;
        bit      firmware_pending_seen;
        bit [15:0] initial_agent_caps;
        int      n_dwords;
        bit [31:0] pattern_dw[$];
        int       i;

        if (!get_sem_vif()) return;

        // Enumerate and discover the OCP Recovery v1.1 functional descriptor
        // through the shared base sequence.
        initialize_ocp_transport();
        sem_vif.clear_i3c_recovery_seen();
        if (sem_vif.i3c_recovery_payload_available !== 1'b0) begin
            `uvm_fatal("OCP_PAYLOAD_ROUTE",
                "I3C payload-available source is not quiescent for USB route validation.")
        end
        if (sem_vif.recovery_payload_available !== 1'b0) begin
            `uvm_error("OCP_PAYLOAD_ROUTE",
                "USB recovery payload_available was high before the image transfer.")
        end
        sem_vif.clear_recovery_payload_available_seen();

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
        // PROT_CAP magic per OCP Recovery v1.1 sec 9.2 (uses the
        // shared OCP_PROT_CAP_MAGIC localparam, common to sequence and scoreboard).
        if (prot_cap.size() < 8) begin
            `uvm_error("OCPREC",
                $sformatf("PROT_CAP returned only %0d bytes; expected >= 8 for magic string.",
                          prot_cap.size()))
        end else begin
            for (int j = 0; j < 8; j++) begin
                if (prot_cap[j] !== OCP_SPEC_PROT_CAP_MAGIC[j]) begin
                    `uvm_error("OCPREC",
                        $sformatf("PROT_CAP magic byte %0d mismatch: exp=0x%02h got=0x%02h",
                                  j, OCP_SPEC_PROT_CAP_MAGIC[j], prot_cap[j]))
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
            if ((prot_cap[OCP_OFF_PC_VERSION_MAJOR] !==
                    OCP_SPEC_VERSION_MAJOR) ||
                (prot_cap[OCP_OFF_PC_VERSION_MINOR] !==
                    OCP_SPEC_VERSION_MINOR)) begin
                `uvm_error("OCPREC",
                    $sformatf("PROT_CAP version mismatch: got=0x%04h expected 1.1.",
                              prot_version))
            end
            agent_caps = {prot_cap[11], prot_cap[10]};
            initial_agent_caps = agent_caps;
            if ((agent_caps & OCP_CAP_RESERVED_MASK) != '0) begin
                `uvm_error("OCPREC",
                    $sformatf("PROT_CAP reserved capability bits are nonzero: 0x%04h.",
                              agent_caps & OCP_CAP_RESERVED_MASK))
            end
            if (!agent_caps[OCP_CAP_IDENTIFICATION] ||
                !agent_caps[OCP_CAP_DEVICE_STATUS] ||
                !(agent_caps[OCP_CAP_LOCAL_C_IMAGE] ||
                  agent_caps[OCP_CAP_PUSH_C_IMAGE])) begin
                `uvm_error("OCPREC",
                    $sformatf("PROT_CAP mandatory capabilities are missing: 0x%04h.",
                              agent_caps))
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

        // 4c-4d. Firmware publication begins after the MCU mailbox handoff,
        // which can lag USB configuration. Poll the two firmware-owned status
        // commands together instead of sampling a legal pre-publication value.
        wait_firmware_ready_status();

        // ---------------------------------------------------------------------
        // Unsupported-command PROTOCOL_ERROR negative check (OCP
        //     Recovery v1.1 Sec 9.1: "an unsupported command MUST set an
        //     unsupported error condition in the DEVICE_STATUS"; Sec 9.2 Tbl
        //     9-6 byte 1 = 0x01 "Unsupported/Write Command", clear-on-read).
        //     INDIRECT_CTRL is the direct CMS-memory window, which
        //     this FIFO-only transport does not implement (not
        //     advertised: AGENT_CAPS bit5 = 0).  The device STALLs the request
        //     (a legal "unsupported" response; the control pipe auto-clears the
        //     stall on the next SETUP per USB 2.0 sec 8.5.3.4) and latches
        //     PROTOCOL_ERROR = 0x01.
        //     Done here before the recovery flow so the Recovery Agent's
        //     clear-on-read behavior is checked before later status polling.
        //     Firmware reads are intentionally non-destructive; only a
        //     completed USB DEVICE_STATUS read may clear PROTOCOL_ERROR.
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
                    "Unsupported-command check: PROTOCOL_ERROR cleared to 0x00 on DEVICE_STATUS read (clear-on-read).",
                    UVM_NONE)
            end
        end

        // ---------------------------------------------------------------------
        // Host-RO write PROTOCOL_ERROR negative check (OCP Recovery v1.1
        //     Sec 9.1: "Writing to a read only command (e.g. PROT_CAP) MUST
        //     generate an 'unsupported command' error in the DEVICE_STATUS").
        //     PROT_CAP capability sub-fields are firmware-configurable
        //     (sw=rw); the USB host must remain RO. Verify: (a) a
        //     USB-host write to PROT_CAP raises PROTOCOL_ERROR=0x01
        //     (clear-on-read, same as the unsupported-command check above), and (b) the write has no effect --
        //     AGENT_CAPS read back unchanged from OCP_PROT_CAP_AGENT_CAPS_EXP.
        //     Also covers INDIRECT_FIFO_STATUS (Sec 9.2 cmd=46, r/w=ro): a
        //     host write there is likewise rejected (the prior cms_fifo
        //     write-1-to-clear extension was removed as non-spec-conformant
        //     and unused by any test/firmware).
        //     Done here before the recovery flow so the Recovery Agent's
        //     clear-on-read behavior is checked before later status polling.
        //     Firmware reads are intentionally non-destructive.
        // ---------------------------------------------------------------------
        begin
            bit [7:0] ds_proto_r7[$];
            bit [7:0] ds_proto_r7_clr[$];
            bit [7:0] prot_cap_after[$];

            // (a) USB-host write to PROT_CAP (arbitrary non-zero payload
            // targeting the AGENT_CAPS bytes 10-11) must be rejected.
            prot_cap_wr_payload.delete();
            prot_cap_wr_payload = '{8'hFF, 8'hFF, 8'hFF, 8'hFF,
                                     8'hFF, 8'hFF, 8'hFF, 8'hFF,
                                     8'hFF, 8'hFF, 8'hFF, 8'hFF};
            resp_q.delete();
            ocp_class_xfer(.dir_in(1'b0),
                           .cmd_code(OCP_REC_CMD_PROT_CAP),
                           .wlength(16'(prot_cap_wr_payload.size())),
                           .payload_bytes(prot_cap_wr_payload),
                           .resp_bytes(resp_q),
                           .label("OCPREC_PROT_CAP_HOST_WRITE_REJECTED"));

            empty_q.delete();
            ds_proto_r7.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(ds_proto_r7),
                           .label("OCPREC_DEVICE_STATUS_PROTOERR_R7_PROTCAP"));
            if (ds_proto_r7.size() < 2) begin
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS after PROT_CAP host write returned %0d bytes; need >= 2 to read PROTOCOL_ERROR (byte 1).",
                              ds_proto_r7.size()))
            end else if (ds_proto_r7[1] !== 8'h01) begin
                `uvm_error("OCPREC",
                    $sformatf("PROTOCOL_ERROR not set after USB-host write to PROT_CAP: DEVICE_STATUS[1]=0x%02h, expected 0x01 (OCP Recovery v1.1 Sec 9.1 write-to-RO, R7).",
                              ds_proto_r7[1]))
            end else begin
                `uvm_info("OCPREC",
                    "PROTOCOL_ERROR=0x01 correctly set after USB-host write to PROT_CAP (OCP Recovery v1.1 Sec 9.1).",
                    UVM_NONE)
            end

            // Clear-on-read check (same semantics as the unsupported-command check above).
            empty_q.delete();
            ds_proto_r7_clr.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(ds_proto_r7_clr),
                           .label("OCPREC_DEVICE_STATUS_PROTOERR_R7_PROTCAP_CLR"));
            if (ds_proto_r7_clr.size() < 2) begin
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS (PROT_CAP write-reject clear check) returned %0d bytes; need >= 2.",
                              ds_proto_r7_clr.size()))
            end else if (ds_proto_r7_clr[1] !== 8'h00) begin
                `uvm_error("OCPREC",
                    $sformatf("PROTOCOL_ERROR did not clear on read after PROT_CAP host-write check: DEVICE_STATUS[1]=0x%02h, expected 0x00.",
                              ds_proto_r7_clr[1]))
            end

            // (b) Confirm the rejected write had no effect: AGENT_CAPS must
            // still read back the RESET default, not the 0xFFFF written above.
            empty_q.delete();
            prot_cap_after.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_PROT_CAP),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(prot_cap_after),
                           .label("OCPREC_PROT_CAP_UNCHANGED_AFTER_HOST_WRITE"));
            if (prot_cap_after.size() < 12) begin
                `uvm_error("OCPREC",
                    $sformatf("PROT_CAP (post host-write check) returned %0d bytes; need >= 12.",
                              prot_cap_after.size()))
            end else begin
                logic [15:0] agent_caps_after;
                agent_caps_after = {prot_cap_after[11], prot_cap_after[10]};
                if (agent_caps_after !== initial_agent_caps) begin
                    `uvm_error("OCPREC",
                        $sformatf("PROT_CAP AGENT_CAPS changed after rejected USB-host write: before=0x%04h after=0x%04h.",
                                  initial_agent_caps, agent_caps_after))
                end else begin
                    `uvm_info("OCPREC",
                        "PROT_CAP AGENT_CAPS unchanged after rejected USB-host write, as expected.",
                        UVM_NONE)
                end
            end

            // (c) INDIRECT_FIFO_STATUS is also strictly host-RO (Sec 9.2
            // cmd=46). A 1-byte write must likewise raise PROTOCOL_ERROR.
            empty_q.delete();
            resp_q.delete();
            ocp_class_xfer(.dir_in(1'b0),
                           .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_STATUS),
                           .wlength(16'd1),
                           .payload_bytes(empty_q),
                           .resp_bytes(resp_q),
                           .label("OCPREC_INDIRECT_FIFO_STATUS_HOST_WRITE_REJECTED"));

            empty_q.delete();
            ds_proto_r7.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(ds_proto_r7),
                           .label("OCPREC_DEVICE_STATUS_PROTOERR_R7_FIFOSTATUS"));
            if (ds_proto_r7.size() < 2) begin
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS after INDIRECT_FIFO_STATUS host write returned %0d bytes; need >= 2.",
                              ds_proto_r7.size()))
            end else if (ds_proto_r7[1] !== 8'h01) begin
                `uvm_error("OCPREC",
                    $sformatf("PROTOCOL_ERROR not set after USB-host write to INDIRECT_FIFO_STATUS: DEVICE_STATUS[1]=0x%02h, expected 0x01 (Sec 9.1/9.2, R7).",
                              ds_proto_r7[1]))
            end else begin
                `uvm_info("OCPREC",
                    "PROTOCOL_ERROR=0x01 correctly set after USB-host write to INDIRECT_FIFO_STATUS (OCP Recovery v1.1 Sec 9.1/9.2).",
                    UVM_NONE)
            end

            // Clear-on-read for the FIFO_STATUS check.
            empty_q.delete();
            ds_proto_r7_clr.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(ds_proto_r7_clr),
                           .label("OCPREC_DEVICE_STATUS_PROTOERR_R7_FIFOSTATUS_CLR"));
            if (ds_proto_r7_clr.size() < 2) begin
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS (INDIRECT_FIFO_STATUS write-reject clear check) returned %0d bytes; need >= 2.",
                              ds_proto_r7_clr.size()))
            end else if (ds_proto_r7_clr[1] !== 8'h00) begin
                `uvm_error("OCPREC",
                    $sformatf("PROTOCOL_ERROR did not clear on read after INDIRECT_FIFO_STATUS host-write check: DEVICE_STATUS[1]=0x%02h, expected 0x00.",
                              ds_proto_r7_clr[1]))
            end
        end

        // ---------------------------------------------------------------------
        // 5. Streaming-boot-lite phase
        // ---------------------------------------------------------------------

        // 5pre. RECOVERY_CTRL OUT: initiate recovery so the device
        //     Initiate recovery before transferring the image so the device can
        //     enter Recovery Pending after the programmed image is received.
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

        // 5a-rt. INDIRECT_FIFO_CTRL IN read-back. OCP Recovery v1.1
        //     Section 9.2 defines CMS in byte 0 and IMAGE_SIZE in bytes 2..5.
        resp_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_CTRL),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(resp_q),
                       .label("OCPREC_INDIRECT_FIFO_CTRL_RDBK"));
        if (resp_q.size() >= OCP_SPEC_LEN_INDIRECT_FIFO_CTRL) begin
            int unsigned img_sz_rb;
            img_sz_rb = {resp_q[OCP_OFF_IFC_IMG_SIZE_B3],
                         resp_q[OCP_OFF_IFC_IMG_SIZE_B3-1],
                         resp_q[OCP_OFF_IFC_IMG_SIZE_B0+1],
                         resp_q[OCP_OFF_IFC_IMG_SIZE_B0]};
            `uvm_info("OCPREC",
                $sformatf("INDIRECT_FIFO_CTRL read-back: CMS=0x%02h IMAGE_SIZE=%0d (4B units; expected CMS=0, IMAGE_SIZE=12)",
                          resp_q[0], img_sz_rb), UVM_NONE)
            if (resp_q[0] != 8'h00)
                `uvm_error("OCPREC",
                    $sformatf("INDIRECT_FIFO_CTRL.CMS read-back=0x%02h, expected 0x00 (regblock read routing).",
                              resp_q[0]))
            if (img_sz_rb != 32'd12)
                `uvm_error("OCPREC",
                    $sformatf("INDIRECT_FIFO_CTRL.IMAGE_SIZE read-back=%0d, expected 12 DWORDs (regblock read routing / cms_fifo hw=w drive).",
                              img_sz_rb))
        end else begin
            `uvm_error("OCPREC",
                $sformatf("INDIRECT_FIFO_CTRL read-back returned %0d bytes; need %0d.",
                          resp_q.size(), OCP_SPEC_LEN_INDIRECT_FIFO_CTRL))
        end

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
        //       bytes 16..19 : MAX_TRANSFER_SIZE (4-byte units, LE)
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

        // 5d. Poll DEVICE_STATUS until firmware publishes Recovery Pending
        //     after observing payload_available. The bounded loop fails closed
        //     if firmware never advances.
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
            if (dev_status[0] == OCP_DEVICE_STATUS_RECOVERY_PENDING) begin
                recovery_pending_seen = 1'b1;
                break;
            end
            poll_iter++;
            if (poll_iter > 16) begin
                // Fail closed if firmware never advances: this exit
                // path MUST raise an error (uvm_info would be re-routed by
                // +svt_debug_opts and the timeout would slip unnoticed).
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS did not reach 0x04 RECOVERY_PENDING within 16 polls. last dev_status[0]=0x%02h time=%0t",
                              dev_status.size() > 0 ? dev_status[0] : 8'h00,
                              $time))
                break;
            end
            #50us;
        end

        if (recovery_pending_seen) begin
            sem_vif.wait_for_fw_state_bounded(
                OCP_FW_STATE_RECOVERY_PENDING,
                200,
                1us,
                firmware_pending_seen);
            if (!firmware_pending_seen) begin
                `uvm_error("OCP_PAYLOAD_ROUTE",
                    "Firmware Recovery Pending publication was not observed.")
            end else if (!sem_vif.recovery_payload_available_seen) begin
                `uvm_error("OCP_PAYLOAD_ROUTE",
                    "Firmware published Recovery Pending without a USB payload_available assertion.")
            end else if (sem_vif.recovery_payload_observed_at == 0.0) begin
                `uvm_error("OCP_PAYLOAD_ROUTE",
                    "Firmware payload-observed publication timestamp was not captured.")
            end else if (sem_vif.recovery_payload_available_asserted_at >
                         sem_vif.recovery_payload_observed_at) begin
                `uvm_error("OCP_PAYLOAD_ROUTE",
                    $sformatf("USB payload_available asserted at %0t after firmware observed the combined status at %0t.",
                              sem_vif.recovery_payload_available_asserted_at,
                              sem_vif.recovery_payload_observed_at))
            end else if (sem_vif.i3c_recovery_payload_available_seen) begin
                `uvm_error("OCP_PAYLOAD_ROUTE",
                    "I3C payload-available source asserted during USB route validation.")
            end else begin
                `uvm_info("OCP_PAYLOAD_ROUTE",
                    "USB payload_available asserted before firmware published Recovery Pending.",
                    UVM_NONE)
            end

            empty_q.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_RECOVERY_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(rec_status),
                           .label("OCP_FW_RECOVERY_STATUS_PENDING"));
            if ((rec_status.size() < OCP_SPEC_LEN_RECOVERY_STATUS) ||
                (rec_status[OCP_OFF_RS_STATUS_IMAGE_INDEX][3:0] !==
                    OCP_RECOVERY_STATUS_AWAITING_IMAGE)) begin
                `uvm_error("OCP_FW_STATUS",
                    "Firmware Recovery Pending milestone did not preserve RECOVERY_STATUS Awaiting Image.")
            end
        end

        // The Recovery Agent requests activation after the device reports the
        // FIFO image is loaded. Firmware drains and verifies the image before
        // publishing Running Recovery and Recovery Successful.
        if (recovery_pending_seen) begin
            recovery_ctrl_payload =
                '{8'h00, 8'h00, OCP_RC_ACTIVATE_CODE};
            `uvm_info("OCPREC",
                "RECOVERY_CTRL (cmd 0x26) OUT: CMS=0, ImgSel=0, Activate=0x0F. Requesting activation after RECOVERY_PENDING.",
                UVM_NONE)
            ocp_class_xfer(.dir_in(1'b0),
                           .cmd_code(OCP_REC_CMD_RECOVERY_CTRL),
                           .wlength(16'(recovery_ctrl_payload.size())),
                           .payload_bytes(recovery_ctrl_payload),
                           .resp_bytes(resp_q),
                           .label("OCPREC_RECOVERY_CTRL_ACTIVATE"));
        end

        if (sem_vif.i3c_recovery_payload_available_seen) begin
            `uvm_error("OCP_PAYLOAD_ROUTE",
                "I3C payload-available source was not quiescent across the recovery flow.")
        end

        // Keep the sequence objection active while firmware drains and verifies
        // the image, publishes completion status, and signals MCU completion.
        if (recovery_pending_seen) begin
            `uvm_info("OCPREC",
                "DEVICE_STATUS=0x04 RECOVERY_PENDING observed. Holding the main_phase objection so the MCU can complete streaming-boot and report TB_CMD_END_SIM_WITH_SUCCESS (which $finishes the sim). Bounded fail-safe wait engaged.",
                UVM_NONE)
            #200us;
            `uvm_error("OCPREC",
                "Bounded post-RECOVERY_PENDING keep-alive (200us) elapsed without the MCU ending the sim via TB_CMD_END_SIM_WITH_SUCCESS. The streaming-boot handoff did not complete; ending the sequence so the test can report.")
        end

        // Publish the issued transfer count so the scoreboard's
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
