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

`ifndef CALIPTRA_SS_USB_OCP_RECOVERY_BASE_SEQUENCE_SV
`define CALIPTRA_SS_USB_OCP_RECOVERY_BASE_SEQUENCE_SV

typedef enum bit [1:0] {
    OCP_XFER_SUCCESS,
    OCP_XFER_NON_SUCCESS,
    OCP_XFER_ABORTED
} caliptra_ss_usb_ocp_xfer_result_e;

class caliptra_ss_usb_ocp_recovery_base_sequence
    extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_ocp_recovery_base_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    protected svt_usb_agent         host_agent_h;
    protected svt_usb_configuration usb_cfg;
    protected svt_usb_status        shared_status;

    protected int unsigned wMaxRdTransferSize;
    protected int unsigned wMaxWrTransferSize;
    protected bit [15:0]   bcdOCPRecVersion;
    protected int unsigned dev_addr_v;
    protected int unsigned transfers_issued;

    function new(string name = "caliptra_ss_usb_ocp_recovery_base_sequence");
        super.new(name);
        wMaxRdTransferSize = OCP_USB_MIN_TRANSFER_SIZE;
        wMaxWrTransferSize = OCP_USB_MIN_TRANSFER_SIZE;
        bcdOCPRecVersion   = OCP_USB_BCD_VERSION_1P1;
        dev_addr_v         = 1;
        transfers_issued   = 0;
    endfunction

    protected virtual function int get_iface_num();
        caliptra_ss_usb_shared_cfg scfg;
        if (uvm_config_db#(caliptra_ss_usb_shared_cfg)::get(
                null, "", "cfg", scfg)) begin
            return scfg.ocp_recovery_iface_num;
        end
        return 0;
    endfunction

    protected virtual function caliptra_ss_usb_ocp_xfer_result_e
        get_xfer_result(svt_usb_transfer req);
        if ((req == null) || (req.status == svt_sequence_item::ABORTED)) begin
            return OCP_XFER_ABORTED;
        end
        // OCP Recovery v1.1 Section 8.2.5 FIFO writes can change ring state
        // when the OUT DATA stage is accepted, before a later status-stage
        // condition is reflected in the VIP result bitmap. Treat a complete
        // FIFO DATA stage as delivered; subsequent STATUS reads determine how
        // many DWORDs actually advanced WRITE_INDEX.
        if ((req.setup_data_bmrequesttype_dir ==
                svt_usb_types::HOST_TO_DEVICE) &&
            (req.setup_data_w_value[7:0] ==
                OCP_CMD_INDIRECT_FIFO_DATA) &&
            caliptra_ss_usb_out_payload_complete(req)) begin
            return OCP_XFER_SUCCESS;
        end
        if (!caliptra_ss_usb_xfer_successful(req)) begin
            return OCP_XFER_NON_SUCCESS;
        end
        return OCP_XFER_SUCCESS;
    endfunction

    protected virtual function void copy_in_payload(
        input svt_usb_transfer req,
        input int unsigned max_bytes,
        ref bit [7:0] resp_bytes[$]);

        int start_ix;
        int end_ix;

        resp_bytes.delete();
        if ((req == null) || (req.payload == null)) begin
            return;
        end

        start_ix = req.payload_start_ix;
        end_ix   = req.payload_end_ix;
        if ((start_ix < 0) || (end_ix < start_ix) ||
            (end_ix > req.payload.data.size())) begin
            `uvm_error("OCP_BASE",
                $sformatf("Invalid completed payload window [%0d,%0d) for data size %0d.",
                          start_ix, end_ix, req.payload.data.size()))
            return;
        end

        if ((end_ix - start_ix) > max_bytes) begin
            `uvm_error("OCP_BASE",
                $sformatf("Completed payload length %0d exceeds requested maximum %0d.",
                          end_ix - start_ix, max_bytes))
            end_ix = start_ix + max_bytes;
        end

        for (int i = start_ix; i < end_ix; i++) begin
            resp_bytes.push_back(req.payload.data[i]);
        end
    endfunction

    protected virtual function bit [15:0] get_le16(
        ref bit [7:0] bytes[$], input int offset);
        return {bytes[offset + 1], bytes[offset]};
    endfunction

    protected virtual function bit [31:0] get_le32(
        ref bit [7:0] bytes[$], input int offset);
        return {bytes[offset + 3], bytes[offset + 2],
                bytes[offset + 1], bytes[offset]};
    endfunction

    protected virtual task ocp_class_xfer_result(
        input bit dir_in,
        input ocp_cmd_t cmd_code,
        input bit [15:0] wlength,
        ref bit [7:0] payload_bytes[$],
        ref bit [7:0] resp_bytes[$],
        output caliptra_ss_usb_ocp_xfer_result_e result,
        input string label);

        svt_usb_transfer req;
        bit [7:0]        bm_dir;
        bit [15:0]       wvalue_v;
        bit [15:0]       windex_v;
        int              payload_size;

        bm_dir   = dir_in ? svt_usb_types::DEVICE_TO_HOST
                          : svt_usb_types::HOST_TO_DEVICE;
        wvalue_v = {8'h00, cmd_code};
        windex_v = {8'h00, 8'(get_iface_num())};

        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null) begin
            req.cfg = usb_cfg;
        end
        req.fix_anchors(0, 0, 0);

        payload_size = payload_bytes.size();
        if (!dir_in) begin
            req.payload = svt_usb_payload::type_id::create("payload");
            if (req.payload == null) begin
                `uvm_fatal("OCP_BASE",
                    $sformatf("Could not create OUT payload for %s.", label))
            end
            req.payload.data = new[payload_size];
        end

        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == dev_addr_v;
                setup_data_bmrequesttype_dir       == bm_dir;
                setup_data_bmrequesttype_type      == svt_usb_types::CLASS;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_INTERFACE;
                setup_data_brequest                == OCP_BREQUEST_XFER;
                setup_data_w_value                 == wvalue_v;
                setup_data_w_index                 == windex_v;
                setup_data_w_length                == wlength;
                payload_start_ix                   == 0;
                payload_intended_byte_count        == wlength;
                if (!dir_in) {
                    payload.data.size() == payload_size;
                    foreach (payload.data[i]) payload.data[i] == payload_bytes[i];
                }
            }) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("Transfer randomization failed for %s.", label))
        end

        finish_item(req, -1);
        transfers_issued++;
        host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();

        result = get_xfer_result(req);
        if (dir_in && (result == OCP_XFER_SUCCESS)) begin
            copy_in_payload(req, wlength, resp_bytes);
        end else begin
            resp_bytes.delete();
        end

        `uvm_info("OCP_BASE",
            $sformatf("OCP transfer %s cmd=0x%02h dir=%s wLength=%0d result=%s actual_bytes=%0d",
                      label, cmd_code, dir_in ? "IN" : "OUT", wlength,
                      result.name(), resp_bytes.size()),
            UVM_NONE)
    endtask

    protected virtual task ocp_class_xfer(
        input bit dir_in,
        input bit [7:0] cmd_code,
        input bit [15:0] wlength,
        ref bit [7:0] payload_bytes[$],
        ref bit [7:0] resp_bytes[$],
        input string label);

        caliptra_ss_usb_ocp_xfer_result_e result;

        ocp_class_xfer_result(
            dir_in, ocp_cmd_t'(cmd_code), wlength,
            payload_bytes, resp_bytes, result, label);
    endtask

    protected virtual task ocp_try_read(
        input ocp_cmd_t cmd_code,
        ref bit [7:0] resp_bytes[$],
        output caliptra_ss_usb_ocp_xfer_result_e result,
        input string label);

        bit [7:0] empty_payload[$];
        empty_payload.delete();
        ocp_class_xfer_result(
            1'b1, cmd_code, 16'(wMaxRdTransferSize),
            empty_payload, resp_bytes, result, label);
    endtask

    protected virtual task ocp_read(
        input ocp_cmd_t cmd_code,
        ref bit [7:0] resp_bytes[$],
        input string label);

        caliptra_ss_usb_ocp_xfer_result_e result;
        ocp_try_read(cmd_code, resp_bytes, result, label);
        if (result != OCP_XFER_SUCCESS) begin
            `uvm_error("OCP_BASE",
                $sformatf("%s cmd=0x%02h did not complete successfully (%s).",
                          label, cmd_code, result.name()))
        end
    endtask

    protected virtual task ocp_try_write(
        input ocp_cmd_t cmd_code,
        ref bit [7:0] payload_bytes[$],
        output caliptra_ss_usb_ocp_xfer_result_e result,
        input string label);

        bit [7:0] resp_bytes[$];
        if (payload_bytes.size() > wMaxWrTransferSize) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("%s payload length %0d exceeds wMaxWrTransferSize=%0d.",
                          label, payload_bytes.size(), wMaxWrTransferSize))
        end
        ocp_class_xfer_result(
            1'b0, cmd_code, 16'(payload_bytes.size()),
            payload_bytes, resp_bytes, result, label);
    endtask

    protected virtual task ocp_write(
        input ocp_cmd_t cmd_code,
        ref bit [7:0] payload_bytes[$],
        input string label);

        caliptra_ss_usb_ocp_xfer_result_e result;
        ocp_try_write(cmd_code, payload_bytes, result, label);
        if (result != OCP_XFER_SUCCESS) begin
            `uvm_error("OCP_BASE",
                $sformatf("%s cmd=0x%02h did not complete successfully (%s).",
                          label, cmd_code, result.name()))
        end
    endtask

    protected virtual task recovery_ctrl_write(
        input bit [7:0] cms,
        input bit [7:0] image_selection,
        input bit activate,
        input string label);

        bit [7:0] payload[$];

        if (image_selection > 8'h02) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("%s image selection 0x%02h is reserved.",
                          label, image_selection))
        end
        payload = '{
            cms,
            image_selection,
            activate ? OCP_RC_ACTIVATE_CODE : 8'h00
        };
        ocp_write(OCP_CMD_RECOVERY_CTRL, payload, label);
    endtask

    protected virtual task indirect_fifo_ctrl_write(
        input bit [7:0] cms,
        input bit reset_fifo,
        input bit [31:0] image_size_dwords,
        input string label);

        bit [7:0] payload[$];

        payload = '{
            cms,
            reset_fifo ? 8'h01 : 8'h00,
            image_size_dwords[7:0],
            image_size_dwords[15:8],
            image_size_dwords[23:16],
            image_size_dwords[31:24]
        };
        ocp_write(OCP_CMD_INDIRECT_FIFO_CTRL, payload, label);
    endtask

    protected virtual task indirect_fifo_data_try_write(
        ref bit [7:0] payload[$],
        output caliptra_ss_usb_ocp_xfer_result_e result,
        input string label);

        if (payload.size() < OCP_SPEC_MIN_LEN_INDIRECT_FIFO_DATA) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("%s requires at least one payload byte.", label))
        end
        ocp_try_write(OCP_CMD_INDIRECT_FIFO_DATA, payload, result, label);
    endtask

    protected virtual task indirect_fifo_data_write(
        ref bit [7:0] payload[$],
        input string label);

        caliptra_ss_usb_ocp_xfer_result_e result;

        indirect_fifo_data_try_write(payload, result, label);
        if (result != OCP_XFER_SUCCESS) begin
            `uvm_error("OCP_BASE",
                $sformatf("%s cmd=0x%02h did not complete successfully (%s).",
                          label, OCP_CMD_INDIRECT_FIFO_DATA, result.name()))
        end
    endtask

    protected virtual task indirect_fifo_status_read(
        ref bit [7:0] response[$],
        output bit fifo_empty,
        output bit fifo_full,
        output bit [7:0] region_type,
        output bit [31:0] write_index,
        output bit [31:0] read_index,
        output bit [31:0] fifo_size,
        output bit [31:0] max_transfer_dwords,
        input string label);

        ocp_read(OCP_CMD_INDIRECT_FIFO_STATUS, response, label);
        if (response.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS) begin
            `uvm_error("OCP_BASE",
                $sformatf("%s response length=%0d, expected %0d.",
                          label, response.size(),
                          OCP_SPEC_LEN_INDIRECT_FIFO_STATUS))
            fifo_empty          = 1'b0;
            fifo_full           = 1'b0;
            region_type         = '0;
            write_index         = '0;
            read_index          = '0;
            fifo_size           = '0;
            max_transfer_dwords = '0;
            return;
        end

        fifo_empty = (response[OCP_OFF_IFS_STATUS] &
                      OCP_IFS_EMPTY_MASK) != 0;
        fifo_full = (response[OCP_OFF_IFS_STATUS] &
                     OCP_IFS_FULL_MASK) != 0;
        region_type = response[OCP_OFF_IFS_REGION_TYPE];
        write_index = get_le32(response, OCP_OFF_IFS_WRITE_INDEX_B0);
        read_index = get_le32(response, OCP_OFF_IFS_READ_INDEX_B0);
        fifo_size = get_le32(response, OCP_OFF_IFS_FIFO_SIZE_B0);
        max_transfer_dwords =
            get_le32(response, OCP_OFF_IFS_MAX_TRANSFER_B0);
    endtask

    protected virtual task poll_device_status(
        input ocp_device_status_e target_status,
        input int unsigned max_polls,
        input time poll_delay,
        output bit reached_target,
        ref bit [7:0] last_response[$],
        input string label);

        reached_target = 1'b0;
        for (int unsigned poll = 0; poll < max_polls; poll++) begin
            device_status_read_and_check(
                last_response, $sformatf("%s_%0d", label, poll));
            if ((last_response.size() >=
                    OCP_SPEC_MIN_LEN_DEVICE_STATUS) &&
                (last_response[OCP_OFF_DS_STATUS] == target_status)) begin
                reached_target = 1'b1;
                return;
            end
            #(poll_delay);
        end
    endtask

    protected virtual task poll_recovery_status(
        input ocp_recovery_status_e target_status,
        input int unsigned max_polls,
        input time poll_delay,
        output bit reached_target,
        ref bit [7:0] last_response[$],
        input string label);

        reached_target = 1'b0;
        for (int unsigned poll = 0; poll < max_polls; poll++) begin
            ocp_read(OCP_CMD_RECOVERY_STATUS, last_response,
                     $sformatf("%s_%0d", label, poll));
            if ((last_response.size() ==
                    OCP_SPEC_LEN_RECOVERY_STATUS) &&
                (last_response[OCP_OFF_RS_STATUS_IMAGE_INDEX][3:0] ==
                    target_status)) begin
                reached_target = 1'b1;
                return;
            end
            #(poll_delay);
        end
    endtask

    protected virtual task standard_get_configuration_descriptor(
        input int unsigned requested_length,
        ref bit [7:0] descriptor_bytes[$],
        input string label);

        svt_usb_transfer req;
        caliptra_ss_usb_ocp_xfer_result_e result;

        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null) begin
            req.cfg = usb_cfg;
        end
        req.fix_anchors(0, 0, 0);
        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == dev_addr_v;
                setup_data_bmrequesttype_dir       == svt_usb_types::DEVICE_TO_HOST;
                setup_data_bmrequesttype_type      == svt_usb_types::STANDARD;
                setup_data_bmrequesttype_recipient == svt_usb_types::BMREQ_DEVICE;
                setup_data_brequest                == 8'h06;
                setup_data_w_value                 == 16'h0200;
                setup_data_w_index                 == 16'h0000;
                setup_data_w_length                == requested_length;
                payload_start_ix                   == 0;
                payload_intended_byte_count        == requested_length;
            }) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("Transfer randomization failed for %s.", label))
        end
        finish_item(req, -1);
        host_agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();

        result = get_xfer_result(req);
        if (result != OCP_XFER_SUCCESS) begin
            descriptor_bytes.delete();
            `uvm_error("OCP_BASE",
                $sformatf("%s did not complete successfully (%s).",
                          label, result.name()))
            return;
        end
        copy_in_payload(req, requested_length, descriptor_bytes);
    endtask

    protected virtual task discover_functional_descriptor();
        bit [7:0] header[$];
        bit [7:0] descriptor_blob[$];
        int unsigned total_length;
        int offset;
        int entry_length;
        bit found;

        standard_get_configuration_descriptor(9, header, "OCP_CONFIG_HEADER");
        if (header.size() != 9) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("Configuration descriptor header length=%0d, expected 9.",
                          header.size()))
        end

        total_length = get_le16(header, 2);
        if (total_length < 9) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("Configuration wTotalLength=%0d is less than 9.",
                          total_length))
        end
        standard_get_configuration_descriptor(
            total_length, descriptor_blob, "OCP_CONFIG_FULL");

        found  = 1'b0;
        offset = 0;
        while ((offset + 2) <= descriptor_blob.size()) begin
            entry_length = descriptor_blob[offset];
            if ((entry_length < 2) ||
                ((offset + entry_length) > descriptor_blob.size())) begin
                `uvm_fatal("OCP_BASE",
                    $sformatf("Malformed descriptor at offset %0d: length=%0d blob=%0d.",
                              offset, entry_length, descriptor_blob.size()))
            end

            if ((descriptor_blob[offset + OCP_OFF_UFD_TYPE] ==
                    OCP_USB_FUNC_DESC_TYPE) &&
                (entry_length > OCP_OFF_UFD_SUBTYPE) &&
                (descriptor_blob[offset + OCP_OFF_UFD_SUBTYPE] ==
                    OCP_USB_FUNC_DESC_SUBTYPE)) begin

                if (entry_length != OCP_USB_FUNC_DESC_LEN) begin
                    `uvm_fatal("OCP_BASE",
                        $sformatf("OCP functional descriptor length=%0d, expected %0d per OCP Recovery v1.1 Sec 8.5.3.",
                                  entry_length, OCP_USB_FUNC_DESC_LEN))
                end
                if (descriptor_blob[offset + OCP_OFF_UFD_RESERVED] != 8'h00) begin
                    `uvm_error("OCP_BASE",
                        "OCP functional descriptor reserved byte is nonzero.")
                end

                wMaxWrTransferSize = {
                    descriptor_blob[offset + OCP_OFF_UFD_MAX_WR_HI],
                    descriptor_blob[offset + OCP_OFF_UFD_MAX_WR_LO]};
                wMaxRdTransferSize = {
                    descriptor_blob[offset + OCP_OFF_UFD_MAX_RD_HI],
                    descriptor_blob[offset + OCP_OFF_UFD_MAX_RD_LO]};
                bcdOCPRecVersion = {
                    descriptor_blob[offset + OCP_OFF_UFD_BCD_VERSION_HI],
                    descriptor_blob[offset + OCP_OFF_UFD_BCD_VERSION_LO]};
                found = 1'b1;
                break;
            end
            offset += entry_length;
        end

        if (!found) begin
            `uvm_fatal("OCP_BASE",
                "OCP Recovery functional descriptor was not found.")
        end
        if ((wMaxWrTransferSize < OCP_USB_MIN_TRANSFER_SIZE) ||
            (wMaxRdTransferSize < OCP_USB_MIN_TRANSFER_SIZE)) begin
            `uvm_error("OCP_BASE",
                $sformatf("Functional descriptor transfer limits wr=%0d rd=%0d violate the 64-byte minimum in OCP Recovery v1.1 Sec 8.5.",
                          wMaxWrTransferSize, wMaxRdTransferSize))
        end
        if (bcdOCPRecVersion != OCP_USB_BCD_VERSION_1P1) begin
            `uvm_error("OCP_BASE",
                $sformatf("Functional descriptor bcdOCPRecVersion=0x%04h, expected 0x%04h.",
                          bcdOCPRecVersion, OCP_USB_BCD_VERSION_1P1))
        end

        `uvm_info("OCP_BASE",
            $sformatf("Functional descriptor: wMaxWr=%0d wMaxRd=%0d bcdVersion=0x%04h",
                      wMaxWrTransferSize, wMaxRdTransferSize,
                      bcdOCPRecVersion),
            UVM_NONE)
    endtask

    protected virtual task initialize_ocp_transport();
        caliptra_ss_usb_init_sequence init_seq;

        resolve_xfer_handles(host_agent_h, usb_cfg, shared_status);
        init_seq = caliptra_ss_usb_init_sequence::type_id::create("init_seq");
        init_seq.start(p_sequencer, this);
        discover_functional_descriptor();
    endtask

    protected virtual function bit legal_device_id_type(bit [7:0] value);
        case (value)
            OCP_DEVICE_ID_PCI_VENDOR,
            OCP_DEVICE_ID_IANA,
            OCP_DEVICE_ID_UUID,
            OCP_DEVICE_ID_PNP_VENDOR,
            OCP_DEVICE_ID_ACPI_VENDOR,
            OCP_DEVICE_ID_IANA_ENTERPRISE,
            OCP_DEVICE_ID_NVME_MI: return 1'b1;
            default: return 1'b0;
        endcase
    endfunction

    protected virtual function bit legal_device_status(bit [7:0] value);
        case (value)
            OCP_DEVICE_STATUS_PENDING,
            OCP_DEVICE_STATUS_HEALTHY,
            OCP_DEVICE_STATUS_ERROR,
            OCP_DEVICE_STATUS_RECOVERY_MODE,
            OCP_DEVICE_STATUS_RECOVERY_PENDING,
            OCP_DEVICE_STATUS_RUNNING_RECOVERY,
            OCP_DEVICE_STATUS_BOOT_FAILURE,
            OCP_DEVICE_STATUS_FATAL_ERROR: return 1'b1;
            default: return 1'b0;
        endcase
    endfunction

    protected virtual function bit legal_recovery_status(bit [3:0] value);
        case (value)
            OCP_RECOVERY_STATUS_NOT_IN_RECOVERY,
            OCP_RECOVERY_STATUS_AWAITING_IMAGE,
            OCP_RECOVERY_STATUS_BOOTING_IMAGE,
            OCP_RECOVERY_STATUS_SUCCESS,
            OCP_RECOVERY_STATUS_FAILED,
            OCP_RECOVERY_STATUS_AUTH_ERROR,
            OCP_RECOVERY_STATUS_ENTRY_ERROR,
            OCP_RECOVERY_STATUS_INVALID_CMS: return 1'b1;
            default: return 1'b0;
        endcase
    endfunction

    protected virtual task prot_cap_read_and_check(
        output bit [15:0] agent_caps,
        output bit [7:0] cms_count,
        output bit [7:0] heartbeat_period);

        bit [7:0] response[$];
        int unsigned expected_length;
        ocp_read(OCP_CMD_PROT_CAP, response, "OCP_CMD_001_PROT_CAP");

        expected_length = OCP_OFF_PC_HEARTBEAT_PERIOD + 2;
        if (response.size() != expected_length) begin
            `uvm_error("OCP_BASE",
                $sformatf("PROT_CAP length=%0d, expected %0d including the reserved pad byte.",
                          response.size(), expected_length))
            agent_caps      = '0;
            cms_count       = '0;
            heartbeat_period = '0;
            return;
        end

        for (int i = 0; i < 8; i++) begin
            if (response[OCP_OFF_PC_MAGIC_START + i] !==
                    OCP_SPEC_PROT_CAP_MAGIC[i]) begin
                `uvm_error("OCP_BASE",
                    $sformatf("PROT_CAP magic byte %0d expected 0x%02h got 0x%02h.",
                              i, OCP_SPEC_PROT_CAP_MAGIC[i],
                              response[OCP_OFF_PC_MAGIC_START + i]))
            end
        end
        if ((response[OCP_OFF_PC_VERSION_MAJOR] != OCP_SPEC_VERSION_MAJOR) ||
            (response[OCP_OFF_PC_VERSION_MINOR] != OCP_SPEC_VERSION_MINOR)) begin
            `uvm_error("OCP_BASE",
                $sformatf("PROT_CAP version=%0d.%0d, expected %0d.%0d.",
                          response[OCP_OFF_PC_VERSION_MAJOR],
                          response[OCP_OFF_PC_VERSION_MINOR],
                          OCP_SPEC_VERSION_MAJOR, OCP_SPEC_VERSION_MINOR))
        end
        if (response[expected_length-1] != 8'h00) begin
            `uvm_error("OCP_BASE",
                $sformatf("PROT_CAP reserved pad byte expected 0x00, got 0x%02h.",
                          response[expected_length-1]))
        end

        agent_caps = {
            response[OCP_OFF_PC_AGENT_CAPS_HI],
            response[OCP_OFF_PC_AGENT_CAPS_LO]};
        cms_count = response[OCP_OFF_PC_CMS_COUNT];
        heartbeat_period = response[OCP_OFF_PC_HEARTBEAT_PERIOD];

        if ((agent_caps & OCP_CAP_RESERVED_MASK) != '0) begin
            `uvm_error("OCP_BASE",
                $sformatf("PROT_CAP reserved capability bits are nonzero: 0x%04h.",
                          agent_caps & OCP_CAP_RESERVED_MASK))
        end
        if (!agent_caps[OCP_CAP_IDENTIFICATION]) begin
            `uvm_error("OCP_BASE",
                "PROT_CAP does not advertise mandatory DEVICE_ID capability.")
        end
        if (!agent_caps[OCP_CAP_DEVICE_STATUS]) begin
            `uvm_error("OCP_BASE",
                "PROT_CAP does not advertise mandatory DEVICE_STATUS capability.")
        end
        if (!(agent_caps[OCP_CAP_LOCAL_C_IMAGE] ||
              agent_caps[OCP_CAP_PUSH_C_IMAGE])) begin
            `uvm_error("OCP_BASE",
                "PROT_CAP advertises neither mandatory Local C-image nor Push C-image support.")
        end
        if (agent_caps[OCP_CAP_PUSH_C_IMAGE] &&
            !(agent_caps[OCP_CAP_INDIRECT_CTRL] ||
              agent_caps[OCP_CAP_INDIRECT_FIFO])) begin
            `uvm_error("OCP_BASE",
                "PROT_CAP Push C-image capability has no advertised indirect memory transport.")
        end
        if ((agent_caps[OCP_CAP_INDIRECT_CTRL] ||
             agent_caps[OCP_CAP_INDIRECT_FIFO]) && (cms_count == 0)) begin
            `uvm_error("OCP_BASE",
                "PROT_CAP advertises CMS access but reports zero CMS regions.")
        end
    endtask

    protected virtual task device_id_read_and_check();
        bit [7:0] response[$];
        int unsigned vendor_length;

        ocp_read(OCP_CMD_DEVICE_ID, response, "OCP_CMD_002_DEVICE_ID");
        if ((response.size() < OCP_SPEC_MIN_LEN_DEVICE_ID) ||
            (response.size() > OCP_SPEC_MAX_LEN_DEVICE_ID)) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_ID length=%0d is outside the spec range %0d..%0d.",
                          response.size(), OCP_SPEC_MIN_LEN_DEVICE_ID,
                          OCP_SPEC_MAX_LEN_DEVICE_ID))
            return;
        end
        if (!legal_device_id_type(response[OCP_OFF_DID_DESC_TYPE])) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_ID descriptor type 0x%02h is reserved.",
                          response[OCP_OFF_DID_DESC_TYPE]))
        end
        vendor_length = response[OCP_OFF_DID_VENDOR_STRING_LEN];
        if (response.size() != (OCP_OFF_DID_VENDOR_STRING + vendor_length)) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_ID length=%0d is inconsistent with Vendor Specific String Length=%0d.",
                          response.size(), vendor_length))
        end
    endtask

    protected virtual task device_status_read_and_check(
        ref bit [7:0] response[$],
        input string label);

        int unsigned vendor_length;
        bit [15:0] heartbeat;
        bit [15:0] recovery_reason;

        ocp_read(OCP_CMD_DEVICE_STATUS, response, label);
        if ((response.size() < OCP_SPEC_MIN_LEN_DEVICE_STATUS) ||
            (response.size() > OCP_SPEC_MAX_LEN_DEVICE_STATUS)) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_STATUS length=%0d is outside the spec range %0d..%0d.",
                          response.size(), OCP_SPEC_MIN_LEN_DEVICE_STATUS,
                          OCP_SPEC_MAX_LEN_DEVICE_STATUS))
            return;
        end
        if (!legal_device_status(response[OCP_OFF_DS_STATUS])) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_STATUS value 0x%02h is reserved.",
                          response[OCP_OFF_DS_STATUS]))
        end
        heartbeat = get_le16(response, OCP_OFF_DS_HEARTBEAT_LO);
        recovery_reason =
            get_le16(response, OCP_OFF_DS_REC_REASON_LO);
        if (heartbeat > OCP_DEVICE_STATUS_HEARTBEAT_MAX) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_STATUS heartbeat=%0d exceeds 4095.",
                          heartbeat))
        end
        case (response[OCP_OFF_DS_STATUS])
            OCP_DEVICE_STATUS_RECOVERY_MODE,
            OCP_DEVICE_STATUS_RECOVERY_PENDING,
            OCP_DEVICE_STATUS_BOOT_FAILURE: begin
                if ((recovery_reason > OCP_REC_REASON_STANDARD_MAX) &&
                    !((recovery_reason >= OCP_REC_REASON_VENDOR_MIN) &&
                      (recovery_reason <= OCP_REC_REASON_VENDOR_MAX))) begin
                    `uvm_error("OCP_BASE",
                        $sformatf("DEVICE_STATUS=0x%02h populates reserved Recovery Reason 0x%04h.",
                                  response[OCP_OFF_DS_STATUS],
                                  recovery_reason))
                end
            end
            default: ;
        endcase
        vendor_length = response[OCP_OFF_DS_VENDOR_LEN];
        if (vendor_length > OCP_DEVICE_STATUS_VENDOR_LEN_MAX) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_STATUS vendor length=%0d exceeds %0d.",
                          vendor_length, OCP_DEVICE_STATUS_VENDOR_LEN_MAX))
        end
        if (response.size() != (OCP_OFF_DS_VENDOR_START + vendor_length)) begin
            `uvm_error("OCP_BASE",
                $sformatf("DEVICE_STATUS length=%0d is inconsistent with vendor length=%0d.",
                          response.size(), vendor_length))
        end
    endtask

    protected virtual task hw_status_read_and_check();
        bit [7:0] response[$];
        int unsigned vendor_length;

        ocp_read(OCP_CMD_HW_STATUS, response, "OCP_CMD_007_HW_STATUS");
        if ((response.size() < OCP_SPEC_MIN_LEN_HW_STATUS) ||
            (response.size() > OCP_SPEC_MAX_LEN_HW_STATUS)) begin
            `uvm_error("OCP_BASE",
                $sformatf("HW_STATUS length=%0d is outside the spec range %0d..%0d.",
                          response.size(), OCP_SPEC_MIN_LEN_HW_STATUS,
                          OCP_SPEC_MAX_LEN_HW_STATUS))
            return;
        end
        if ((response[OCP_OFF_HW_DEV_STATUS] &
                OCP_HW_STATUS_RESERVED_MASK) != '0) begin
            `uvm_error("OCP_BASE",
                $sformatf("HW_STATUS reserved bits are nonzero: 0x%02h.",
                          response[OCP_OFF_HW_DEV_STATUS]))
        end
        vendor_length = response[OCP_OFF_HW_VENDOR_LEN];
        if (vendor_length > OCP_HW_STATUS_VENDOR_LEN_MAX) begin
            `uvm_error("OCP_BASE",
                $sformatf("HW_STATUS vendor length=%0d exceeds %0d.",
                          vendor_length, OCP_HW_STATUS_VENDOR_LEN_MAX))
        end
        if (response.size() != (OCP_SPEC_MIN_LEN_HW_STATUS + vendor_length)) begin
            `uvm_error("OCP_BASE",
                $sformatf("HW_STATUS length=%0d is inconsistent with vendor length=%0d.",
                          response.size(), vendor_length))
        end
    endtask

    protected virtual task recovery_status_read_and_check();
        bit [7:0] response[$];
        bit [3:0] recovery_status;

        ocp_read(OCP_CMD_RECOVERY_STATUS, response,
                 "OCP_RECOVERY_STATUS_FORMAT");
        if (response.size() != OCP_SPEC_LEN_RECOVERY_STATUS) begin
            `uvm_error("OCP_BASE",
                $sformatf("RECOVERY_STATUS length=%0d, expected %0d.",
                          response.size(), OCP_SPEC_LEN_RECOVERY_STATUS))
            return;
        end
        recovery_status =
            response[OCP_OFF_RS_STATUS_IMAGE_INDEX][3:0];
        if (!legal_recovery_status(recovery_status)) begin
            `uvm_error("OCP_BASE",
                $sformatf("RECOVERY_STATUS value 0x%01h is reserved.",
                          recovery_status))
        end
    endtask

    protected virtual task indirect_fifo_status_read_and_check();
        bit [7:0] response[$];

        ocp_read(OCP_CMD_INDIRECT_FIFO_STATUS, response,
                 "OCP_INDIRECT_FIFO_STATUS_FORMAT");
        if (response.size() != OCP_SPEC_LEN_INDIRECT_FIFO_STATUS) begin
            `uvm_error("OCP_BASE",
                $sformatf("INDIRECT_FIFO_STATUS length=%0d, expected %0d.",
                          response.size(), OCP_SPEC_LEN_INDIRECT_FIFO_STATUS))
            return;
        end
        if ((response[OCP_OFF_IFS_STATUS] &
                OCP_IFS_STATUS_RSVD_MASK) != '0) begin
            `uvm_error("OCP_BASE",
                $sformatf("INDIRECT_FIFO_STATUS reserved status bits are nonzero: 0x%02h.",
                          response[OCP_OFF_IFS_STATUS]))
        end
        if ((response[OCP_OFF_IFS_RESERVED_LO] != 8'h00) ||
            (response[OCP_OFF_IFS_RESERVED_HI] != 8'h00)) begin
            `uvm_error("OCP_BASE",
                "INDIRECT_FIFO_STATUS reserved bytes are nonzero.")
        end
        case (response[OCP_OFF_IFS_REGION_TYPE])
            OCP_REGION_RECOVERY_CODE_WO,
            OCP_REGION_DEBUG_LOG_RO,
            OCP_REGION_VENDOR_WO,
            OCP_REGION_VENDOR_RO,
            OCP_REGION_UNSUPPORTED: ;
            default: `uvm_error("OCP_BASE",
                $sformatf("INDIRECT_FIFO_STATUS region type 0x%02h is reserved.",
                          response[OCP_OFF_IFS_REGION_TYPE]))
        endcase
    endtask

    protected virtual task ocp_expect_protocol_error(
        input bit dir_in,
        input ocp_cmd_t cmd_code,
        ref bit [7:0] payload_bytes[$],
        input ocp_protocol_error_e expected_error,
        input string label);

        bit [7:0] response[$];
        bit [7:0] device_status[$];
        caliptra_ss_usb_ocp_xfer_result_e result;

        if (dir_in) begin
            bit [7:0] empty_payload[$];
            empty_payload.delete();
            ocp_class_xfer_result(
                1'b1, cmd_code, 16'(wMaxRdTransferSize),
                empty_payload, response, result, label);
        end else begin
            ocp_try_write(cmd_code, payload_bytes, result, label);
        end
        if (result == OCP_XFER_ABORTED) begin
            `uvm_error("OCP_BASE",
                $sformatf("%s transfer aborted before the protocol response completed.",
                          label))
        end

        device_status_read_and_check(
            device_status, {label, "_DEVICE_STATUS_SET"});
        if (device_status.size() > OCP_OFF_DS_PROT_ERROR) begin
            if (device_status[OCP_OFF_DS_PROT_ERROR] != expected_error) begin
                `uvm_error("OCP_BASE",
                    $sformatf("%s protocol error=0x%02h, expected 0x%02h.",
                              label,
                              device_status[OCP_OFF_DS_PROT_ERROR],
                              expected_error))
            end
        end

        device_status_read_and_check(
            device_status, {label, "_DEVICE_STATUS_CLEAR"});
        if (device_status.size() > OCP_OFF_DS_PROT_ERROR) begin
            if (device_status[OCP_OFF_DS_PROT_ERROR] !=
                    OCP_PROTOCOL_ERROR_NONE) begin
                `uvm_error("OCP_BASE",
                    $sformatf("%s protocol error did not clear on the RA read: got 0x%02h.",
                              label,
                              device_status[OCP_OFF_DS_PROT_ERROR]))
            end
        end
    endtask

    protected virtual task publish_transfer_count();
        uvm_config_db#(int unsigned)::set(
            null, "*", "ocp_transfers_issued", transfers_issued);
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_RECOVERY_BASE_SEQUENCE_SV
