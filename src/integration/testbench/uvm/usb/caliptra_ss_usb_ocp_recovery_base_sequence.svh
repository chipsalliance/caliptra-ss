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

    typedef bit [7:0] byte_queue_t[$];

    typedef struct {
        bit          empty;
        bit          full;
        bit [7:0]    region_type;
        bit [31:0]   write_index;
        bit [31:0]   read_index;
        bit [31:0]   fifo_size;
        bit [31:0]   max_transfer_dwords;
    } fifo_status_s;

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
    protected caliptra_ss_usb_ping_retry_callback ping_retry_callback;
    protected bit ping_retry_callback_registered;

    protected virtual caliptra_ss_usb_ocp_access_semantics_if sem_vif;

    function new(string name = "caliptra_ss_usb_ocp_recovery_base_sequence");
        super.new(name);
        wMaxRdTransferSize = OCP_USB_MIN_TRANSFER_SIZE;
        wMaxWrTransferSize = OCP_USB_MIN_TRANSFER_SIZE;
        bcdOCPRecVersion   = OCP_USB_BCD_VERSION_1P1;
        dev_addr_v         = 1;
        transfers_issued   = 0;
        ping_retry_callback_registered = 1'b0;
    endfunction

    protected virtual function bit get_sem_vif();
        if (!uvm_config_db#(
                virtual caliptra_ss_usb_ocp_access_semantics_if)::get(
                    null, "uvm_test_top.env",
                    "ocp_access_semantics_if", sem_vif)) begin
            `uvm_fatal("OCP_BASE",
                "ocp_access_semantics_if not found in config_db")
            return 1'b0;
        end
        return 1'b1;
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

    protected virtual function int unsigned bytes_to_dwords(
        input int unsigned byte_count);
        return (byte_count + 3) / 4;
    endfunction

    protected virtual function int unsigned dwords_to_bytes(
        input int unsigned dword_count);
        return dword_count * 4;
    endfunction

    protected virtual function int unsigned legal_max_chunk_dwords(
        input fifo_status_s status);
        int unsigned usb_limit_dwords;

        usb_limit_dwords = wMaxWrTransferSize / 4;
        if (status.max_transfer_dwords < usb_limit_dwords)
            return status.max_transfer_dwords;
        return usb_limit_dwords;
    endfunction

    protected virtual function automatic void slice_image_payload(
        ref byte_queue_t source_bytes,
        input int unsigned start_dword,
        input int unsigned dword_count,
        ref bit [7:0] payload[$]);
        int unsigned byte_index;

        payload.delete();
        for (int unsigned i = 0;
             (i < dwords_to_bytes(dword_count)) &&
             ((dwords_to_bytes(start_dword) + i) < source_bytes.size());
             i++) begin
            byte_index = dwords_to_bytes(start_dword) + i;
            payload.push_back(source_bytes[byte_index]);
        end
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

    protected virtual task configure_ep0_nak_retry_limit(
        input int unsigned retry_limit);
        if ((usb_cfg == null) ||
            (usb_cfg.remote_device_cfg.size() == 0) ||
            (usb_cfg.remote_device_cfg[0].endpoint_cfg.size() == 0)) begin
            `uvm_fatal("OCP_BASE",
                "EP0 configuration is unavailable for NAK retry setup.")
        end
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].
            max_retry_due_to_nak = retry_limit;
        usb_cfg.remote_device_cfg[0].endpoint_cfg[0].
            max_retry_due_to_nak_before_moving_to_next_ep = 1;
        if (!ping_retry_callback_registered) begin
            ping_retry_callback =
                caliptra_ss_usb_ping_retry_callback::type_id::create(
                    "ping_retry_callback");
            uvm_callbacks#(
                svt_usb_protocol,
                svt_usb_protocol_callbacks)::add(
                    host_agent_h.prot, ping_retry_callback);
            ping_retry_callback_registered = 1'b1;
        end
        host_agent_h.reconfigure(usb_cfg);
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

    protected virtual task prepare_fifo_image(
        input bit [7:0] cms,
        input bit [7:0] image_selection,
        input bit [31:0] image_size_dwords,
        input string recovery_ctrl_label,
        input string fifo_ctrl_label);

        recovery_ctrl_write(
            cms, image_selection, 1'b0, recovery_ctrl_label);
        indirect_fifo_ctrl_write(
            cms, 1'b1, image_size_dwords, fifo_ctrl_label);
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

    protected virtual task read_fifo_status(
        output fifo_status_s status,
        input string label);
        bit [7:0] response[$];

        indirect_fifo_status_read(
            response, status.empty, status.full, status.region_type,
            status.write_index, status.read_index, status.fifo_size,
            status.max_transfer_dwords, label);
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

    protected virtual task prepare_usb_route_validation();
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
    endtask

    protected virtual task read_check_recovery_capabilities(
        input string label,
        output bit [15:0] initial_agent_caps);

        bit [7:0] empty_q[$];
        bit [7:0] prot_cap[$];

        initial_agent_caps = '0;
        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_PROT_CAP),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(prot_cap),
                       .label(label));
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
    endtask

    protected virtual task read_log_device_id(input string label);
        bit [7:0] empty_q[$];
        bit [7:0] dev_id[$];

        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_ID),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(dev_id),
                       .label(label));
        `uvm_info("OCPREC",
            $sformatf("DEVICE_ID returned %0d bytes; first 4: 0x%02h 0x%02h 0x%02h 0x%02h",
                      dev_id.size(),
                      dev_id.size() > 0 ? dev_id[0] : 8'h00,
                      dev_id.size() > 1 ? dev_id[1] : 8'h00,
                      dev_id.size() > 2 ? dev_id[2] : 8'h00,
                      dev_id.size() > 3 ? dev_id[3] : 8'h00),
            UVM_NONE)
    endtask

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

    protected virtual task check_unsupported_indirect_ctrl_protocol_error(
        input string label_prefix = "OCPREC",
        input string report_id = "OCPREC");
        bit [7:0] empty_q[$];
        bit [7:0] unsup_resp[$];
        bit [7:0] ds_proto[$];
        bit [7:0] ds_proto_clr[$];

        empty_q.delete();
        unsup_resp.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_INDIRECT_CTRL),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(unsup_resp),
                       .label({label_prefix, "_UNSUPPORTED_INDIRECT_CTRL"}));

        empty_q.delete();
        ds_proto.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(ds_proto),
                       .label({label_prefix, "_DEVICE_STATUS_PROTOERR"}));
        if (ds_proto.size() < 2) begin
            `uvm_error(report_id,
                $sformatf("DEVICE_STATUS after unsupported command returned %0d bytes; need >= 2 to read PROTOCOL_ERROR (byte 1).",
                          ds_proto.size()))
        end else if (ds_proto[1] !== 8'h01) begin
            `uvm_error(report_id,
                $sformatf("PROTOCOL_ERROR not set after unsupported command 0x29: DEVICE_STATUS[1]=0x%02h, expected 0x01 (OCP Recovery v1.1 Sec 9.1 / Sec 9.2).",
                          ds_proto[1]))
        end else begin
            `uvm_info(report_id,
                "V2: PROTOCOL_ERROR=0x01 correctly set after unsupported command 0x29 (OCP Recovery v1.1 Sec 9.1).",
                UVM_NONE)
        end

        empty_q.delete();
        ds_proto_clr.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(ds_proto_clr),
                       .label({label_prefix, "_DEVICE_STATUS_PROTOERR_CLR"}));
        if (ds_proto_clr.size() < 2) begin
            `uvm_error(report_id,
                $sformatf("DEVICE_STATUS (clear check) returned %0d bytes; need >= 2.",
                          ds_proto_clr.size()))
        end else if (ds_proto_clr[1] !== 8'h00) begin
            `uvm_error(report_id,
                $sformatf("PROTOCOL_ERROR did not clear on read: DEVICE_STATUS[1]=0x%02h, expected 0x00 (OCP Recovery v1.1 Sec 9.1 clear-on-read).",
                          ds_proto_clr[1]))
        end else begin
            `uvm_info(report_id,
                "Unsupported-command check: PROTOCOL_ERROR cleared to 0x00 on DEVICE_STATUS read (clear-on-read).",
                UVM_NONE)
        end
    endtask

    protected virtual task check_rejected_prot_cap_write(
        input bit [15:0] initial_agent_caps,
        input string label_prefix = "OCPREC",
        input string report_id = "OCPREC");

        bit [7:0] empty_q[$];
        bit [7:0] resp_q[$];
        bit [7:0] prot_cap_wr_payload[$];
        bit [7:0] ds_proto_r7[$];
        bit [7:0] ds_proto_r7_clr[$];
        bit [7:0] prot_cap_after[$];

        prot_cap_wr_payload = '{8'hFF, 8'hFF, 8'hFF, 8'hFF,
                                 8'hFF, 8'hFF, 8'hFF, 8'hFF,
                                 8'hFF, 8'hFF, 8'hFF, 8'hFF};
        resp_q.delete();
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_PROT_CAP),
                       .wlength(16'(prot_cap_wr_payload.size())),
                       .payload_bytes(prot_cap_wr_payload),
                       .resp_bytes(resp_q),
                       .label({label_prefix,
                               "_PROT_CAP_HOST_WRITE_REJECTED"}));

        empty_q.delete();
        ds_proto_r7.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(ds_proto_r7),
                       .label({label_prefix,
                               "_DEVICE_STATUS_PROTOERR_R7_PROTCAP"}));
        if (ds_proto_r7.size() < 2) begin
            `uvm_error(report_id,
                $sformatf("DEVICE_STATUS after PROT_CAP host write returned %0d bytes; need >= 2 to read PROTOCOL_ERROR (byte 1).",
                          ds_proto_r7.size()))
        end else if (ds_proto_r7[1] !== 8'h01) begin
            `uvm_error(report_id,
                $sformatf("PROTOCOL_ERROR not set after USB-host write to PROT_CAP: DEVICE_STATUS[1]=0x%02h, expected 0x01 (OCP Recovery v1.1 Sec 9.1 write-to-RO, R7).",
                          ds_proto_r7[1]))
        end else begin
            `uvm_info(report_id,
                "PROTOCOL_ERROR=0x01 correctly set after USB-host write to PROT_CAP (OCP Recovery v1.1 Sec 9.1).",
                UVM_NONE)
        end

        empty_q.delete();
        ds_proto_r7_clr.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(ds_proto_r7_clr),
                       .label({label_prefix,
                               "_DEVICE_STATUS_PROTOERR_R7_PROTCAP_CLR"}));
        if (ds_proto_r7_clr.size() < 2) begin
            `uvm_error(report_id,
                $sformatf("DEVICE_STATUS (PROT_CAP write-reject clear check) returned %0d bytes; need >= 2.",
                          ds_proto_r7_clr.size()))
        end else if (ds_proto_r7_clr[1] !== 8'h00) begin
            `uvm_error(report_id,
                $sformatf("PROTOCOL_ERROR did not clear on read after PROT_CAP host-write check: DEVICE_STATUS[1]=0x%02h, expected 0x00.",
                          ds_proto_r7_clr[1]))
        end

        empty_q.delete();
        prot_cap_after.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_PROT_CAP),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(prot_cap_after),
                       .label({label_prefix,
                               "_PROT_CAP_UNCHANGED_AFTER_HOST_WRITE"}));
        if (prot_cap_after.size() < 12) begin
            `uvm_error(report_id,
                $sformatf("PROT_CAP (post host-write check) returned %0d bytes; need >= 12.",
                          prot_cap_after.size()))
        end else begin
            logic [15:0] agent_caps_after;
            agent_caps_after = {prot_cap_after[11], prot_cap_after[10]};
            if (agent_caps_after !== initial_agent_caps) begin
                `uvm_error(report_id,
                    $sformatf("PROT_CAP AGENT_CAPS changed after rejected USB-host write: before=0x%04h after=0x%04h.",
                              initial_agent_caps, agent_caps_after))
            end else begin
                `uvm_info(report_id,
                    "PROT_CAP AGENT_CAPS unchanged after rejected USB-host write, as expected.",
                    UVM_NONE)
            end
        end
    endtask

    protected virtual task check_rejected_fifo_status_write(
        input string label_prefix = "OCPREC",
        input string report_id = "OCPREC",
        input bit send_payload = 1'b0,
        input bit verify_unchanged = 1'b0);
        bit [7:0] empty_q[$];
        bit [7:0] write_payload[$];
        bit [7:0] resp_q[$];
        bit [7:0] ds_proto_r7[$];
        bit [7:0] ds_proto_r7_clr[$];
        bit [7:0] fifo_status_before[$];
        bit [7:0] fifo_status_after[$];
        bit status_unchanged;

        empty_q.delete();
        write_payload.delete();
        if (send_payload)
            write_payload.push_back(8'hFF);
        if (verify_unchanged) begin
            ocp_read(
                OCP_REC_CMD_INDIRECT_FIFO_STATUS,
                fifo_status_before,
                {label_prefix, "_INDIRECT_FIFO_STATUS_BEFORE"});
        end
        resp_q.delete();
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_STATUS),
                       .wlength(16'd1),
                       .payload_bytes(write_payload),
                       .resp_bytes(resp_q),
                       .label({label_prefix,
                               "_INDIRECT_FIFO_STATUS_HOST_WRITE_REJECTED"}));

        empty_q.delete();
        ds_proto_r7.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(ds_proto_r7),
                       .label({label_prefix,
                               "_DEVICE_STATUS_PROTOERR_R7_FIFOSTATUS"}));
        if (ds_proto_r7.size() < 2) begin
            `uvm_error(report_id,
                $sformatf("DEVICE_STATUS after INDIRECT_FIFO_STATUS host write returned %0d bytes; need >= 2.",
                          ds_proto_r7.size()))
        end else if (ds_proto_r7[1] !== 8'h01) begin
            `uvm_error(report_id,
                $sformatf("PROTOCOL_ERROR not set after USB-host write to INDIRECT_FIFO_STATUS: DEVICE_STATUS[1]=0x%02h, expected 0x01 (Sec 9.1/9.2, R7).",
                          ds_proto_r7[1]))
        end else begin
            `uvm_info(report_id,
                "PROTOCOL_ERROR=0x01 correctly set after USB-host write to INDIRECT_FIFO_STATUS (OCP Recovery v1.1 Sec 9.1/9.2).",
                UVM_NONE)
        end

        empty_q.delete();
        ds_proto_r7_clr.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(ds_proto_r7_clr),
                       .label({label_prefix,
                               "_DEVICE_STATUS_PROTOERR_R7_FIFOSTATUS_CLR"}));
        if (ds_proto_r7_clr.size() < 2) begin
            `uvm_error(report_id,
                $sformatf("DEVICE_STATUS (INDIRECT_FIFO_STATUS write-reject clear check) returned %0d bytes; need >= 2.",
                          ds_proto_r7_clr.size()))
        end else if (ds_proto_r7_clr[1] !== 8'h00) begin
            `uvm_error(report_id,
                $sformatf("PROTOCOL_ERROR did not clear on read after INDIRECT_FIFO_STATUS host-write check: DEVICE_STATUS[1]=0x%02h, expected 0x00.",
                          ds_proto_r7_clr[1]))
        end

        if (verify_unchanged) begin
            ocp_read(
                OCP_REC_CMD_INDIRECT_FIFO_STATUS,
                fifo_status_after,
                {label_prefix, "_INDIRECT_FIFO_STATUS_AFTER"});
            status_unchanged =
                fifo_status_after.size() == fifo_status_before.size();
            if (status_unchanged) begin
                foreach (fifo_status_before[i]) begin
                    if (fifo_status_after[i] !== fifo_status_before[i])
                        status_unchanged = 1'b0;
                end
            end
            if (!status_unchanged) begin
                `uvm_error(report_id,
                    $sformatf({"INDIRECT_FIFO_STATUS changed after rejected ",
                               "host write: before=%p after=%p."},
                              fifo_status_before, fifo_status_after))
            end else begin
                `uvm_info(report_id,
                    "INDIRECT_FIFO_STATUS unchanged after rejected host write.",
                    UVM_NONE)
            end
        end
    endtask

    protected virtual task initiate_recovery(
        input bit [7:0] cms,
        input bit [7:0] image_selection,
        input string label);

        bit [7:0] payload[$];
        bit [7:0] response[$];

        payload = '{cms, image_selection, 8'h00};
        `uvm_info("OCPREC",
            $sformatf({"RECOVERY_CTRL (cmd 0x26) OUT: CMS=%0d, ",
                       "ImgSel=%0d, Activate=0 (sec 9.2)."},
                      cms, image_selection),
            UVM_NONE)
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_RECOVERY_CTRL),
                       .wlength(16'(payload.size())),
                       .payload_bytes(payload),
                       .resp_bytes(response),
                       .label(label));
    endtask

    protected virtual task prepare_fifo_control(
        input bit [7:0] cms,
        input int unsigned image_size_dwords,
        input string label);

        bit [7:0] payload[$];
        bit [7:0] response[$];

        payload = '{cms, 8'h01,
                    image_size_dwords[7:0],
                    image_size_dwords[15:8],
                    image_size_dwords[23:16],
                    image_size_dwords[31:24]};
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_CTRL),
                       .wlength(16'(payload.size())),
                       .payload_bytes(payload),
                       .resp_bytes(response),
                       .label(label));
    endtask

    protected virtual task check_fifo_control_readback(
        input bit [7:0] expected_cms,
        input int unsigned expected_image_size_dwords,
        input string label);

        bit [7:0] empty_q[$];
        bit [7:0] response[$];

        response.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_CTRL),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(response),
                       .label(label));
        if (response.size() >= OCP_SPEC_LEN_INDIRECT_FIFO_CTRL) begin
            int unsigned img_sz_rb;
            img_sz_rb = {response[OCP_OFF_IFC_IMG_SIZE_B3],
                         response[OCP_OFF_IFC_IMG_SIZE_B3-1],
                         response[OCP_OFF_IFC_IMG_SIZE_B0+1],
                         response[OCP_OFF_IFC_IMG_SIZE_B0]};
            `uvm_info("OCPREC",
                $sformatf({"INDIRECT_FIFO_CTRL read-back: CMS=0x%02h ",
                           "IMAGE_SIZE=%0d (4B units; expected CMS=0x%02h, ",
                           "IMAGE_SIZE=%0d)"},
                          response[0], img_sz_rb, expected_cms,
                          expected_image_size_dwords), UVM_NONE)
            if (response[0] != expected_cms)
                `uvm_error("OCPREC",
                    $sformatf({"INDIRECT_FIFO_CTRL.CMS read-back=0x%02h, ",
                               "expected 0x%02h (regblock read routing)."},
                              response[0], expected_cms))
            if (img_sz_rb != expected_image_size_dwords)
                `uvm_error("OCPREC",
                    $sformatf({"INDIRECT_FIFO_CTRL.IMAGE_SIZE read-back=%0d, ",
                               "expected %0d DWORDs (regblock read routing / ",
                               "cms_fifo hw=w drive)."},
                              img_sz_rb, expected_image_size_dwords))
        end else begin
            `uvm_error("OCPREC",
                $sformatf("INDIRECT_FIFO_CTRL read-back returned %0d bytes; need %0d.",
                          response.size(), OCP_SPEC_LEN_INDIRECT_FIFO_CTRL))
        end
    endtask

    protected virtual task automatic build_le_dword_image(
        ref bit [31:0] pattern_dwords[$],
        output bit [7:0] image_bytes[$]);

        image_bytes.delete();
        foreach (pattern_dwords[j]) begin
            image_bytes.push_back(pattern_dwords[j][ 7: 0]);
            image_bytes.push_back(pattern_dwords[j][15: 8]);
            image_bytes.push_back(pattern_dwords[j][23:16]);
            image_bytes.push_back(pattern_dwords[j][31:24]);
        end
    endtask

    protected virtual task automatic build_default_recovery_image(
        input int unsigned image_size_dwords,
        output bit [7:0] image_bytes[$]);

        bit [31:0] pattern_dwords[$];

        pattern_dwords.push_back(32'hDEADBEEF);
        pattern_dwords.push_back(32'hCAFEBABE);
        pattern_dwords.push_back(32'h12345678);
        pattern_dwords.push_back(32'h9ABCDEF0);
        for (int j = pattern_dwords.size(); j < image_size_dwords; j++)
            pattern_dwords.push_back(32'h00000010 + j);
        build_le_dword_image(pattern_dwords, image_bytes);
    endtask

    protected virtual task automatic stream_fifo_image(
        ref bit [7:0] image_bytes[$],
        input string label);

        bit [7:0] response[$];
        fifo_status_s status;
        int unsigned image_dwords;

        read_fifo_status(status, {label, "_SINGLE_BATCH_STATUS"});
        image_dwords = bytes_to_dwords(image_bytes.size());
        if ((status.fifo_size == 0) ||
            (status.max_transfer_dwords == 0)) begin
            `uvm_fatal("OCPREC",
                $sformatf({"%s cannot validate single-batch limits: ",
                           "FIFO_SIZE=%0d MAX_TRANSFER_SIZE=%0d."},
                          label, status.fifo_size,
                          status.max_transfer_dwords))
        end
        if ((image_bytes.size() > wMaxWrTransferSize) ||
            (image_dwords > status.max_transfer_dwords) ||
            (image_dwords > status.fifo_size)) begin
            `uvm_fatal("OCPREC",
                $sformatf({"%s image does not fit one FIFO transfer/batch: ",
                           "bytes=%0d dwords=%0d wMaxWrTransferSize=%0d ",
                           "MAX_TRANSFER_SIZE=%0d FIFO_SIZE=%0d."},
                          label, image_bytes.size(), image_dwords,
                          wMaxWrTransferSize, status.max_transfer_dwords,
                          status.fifo_size))
        end
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_DATA),
                       .wlength(16'(image_bytes.size())),
                       .payload_bytes(image_bytes),
                       .resp_bytes(response),
                       .label(label));
    endtask

    protected virtual task check_fifo_status(
        input int unsigned expected_write_index,
        input string label);

        bit [7:0] empty_q[$];
        bit [7:0] fifo_status[$];

        empty_q.delete();
        ocp_class_xfer(.dir_in(1'b1),
                       .cmd_code(OCP_REC_CMD_INDIRECT_FIFO_STATUS),
                       .wlength(16'(wMaxRdTransferSize)),
                       .payload_bytes(empty_q),
                       .resp_bytes(fifo_status),
                       .label(label));
        if (fifo_status.size() >= 8) begin
            int unsigned wr_idx;
            wr_idx = {fifo_status[7], fifo_status[6],
                      fifo_status[5], fifo_status[4]};
            `uvm_info("OCPREC",
                $sformatf("INDIRECT_FIFO_STATUS: EMPTY=%0d FULL=%0d WRITE_INDEX=%0d (4B units; expected %0d)",
                          fifo_status[0], fifo_status[1], wr_idx,
                          expected_write_index),
                UVM_NONE)
            if (wr_idx != expected_write_index) begin
                `uvm_error("OCPREC",
                    $sformatf("INDIRECT_FIFO_STATUS.WRITE_INDEX=%0d, expected %0d after pushing %0d dwords (sec 9.2).",
                              wr_idx, expected_write_index,
                              expected_write_index))
            end
        end else begin
            `uvm_error("OCPREC",
                $sformatf("INDIRECT_FIFO_STATUS returned %0d bytes; need >= 8 to extract WRITE_INDEX (sec 9.2).",
                          fifo_status.size()))
        end
    endtask

    protected virtual task wait_for_recovery_pending(
        output bit recovery_pending_seen);

        bit [7:0] empty_q[$];
        bit [7:0] dev_status[$];
        int poll_iter;

        poll_iter = 0;
        recovery_pending_seen = 1'b0;
        forever begin
            empty_q.delete();
            ocp_class_xfer(.dir_in(1'b1),
                           .cmd_code(OCP_REC_CMD_DEVICE_STATUS),
                           .wlength(16'(wMaxRdTransferSize)),
                           .payload_bytes(empty_q),
                           .resp_bytes(dev_status),
                           .label($sformatf("OCPREC_DEVICE_STATUS_poll%0d",
                                            poll_iter)));
            if (dev_status.size() < 1) begin
                `uvm_error("OCPREC",
                    "DEVICE_STATUS poll returned 0 bytes.")
                break;
            end
            `uvm_info("OCPREC",
                $sformatf("Polling DEVICE_STATUS[0]=0x%02h iter=%0d (sec 9.2).",
                          dev_status[0], poll_iter),
                UVM_NONE)
            if (dev_status[0] == OCP_DEVICE_STATUS_RECOVERY_PENDING) begin
                recovery_pending_seen = 1'b1;
                break;
            end
            poll_iter++;
            if (poll_iter > 16) begin
                `uvm_error("OCPREC",
                    $sformatf("DEVICE_STATUS did not reach 0x04 RECOVERY_PENDING within 16 polls. last dev_status[0]=0x%02h time=%0t",
                              dev_status.size() > 0 ? dev_status[0] : 8'h00,
                              $time))
                break;
            end
            #50us;
        end
    endtask

    protected virtual task check_usb_route_at_recovery_pending();
        bit firmware_pending_seen;
        bit [7:0] empty_q[$];
        bit [7:0] rec_status[$];

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
    endtask

    protected virtual task activate_recovery(
        input bit [7:0] cms,
        input bit [7:0] image_selection,
        input string label);

        bit [7:0] payload[$];
        bit [7:0] response[$];

        payload = '{cms, image_selection, OCP_RC_ACTIVATE_CODE};
        `uvm_info("OCPREC",
            $sformatf({"RECOVERY_CTRL (cmd 0x26) OUT: CMS=%0d, ",
                       "ImgSel=%0d, Activate=0x%02h."},
                      cms, image_selection, OCP_RC_ACTIVATE_CODE),
            UVM_NONE)
        ocp_class_xfer(.dir_in(1'b0),
                       .cmd_code(OCP_REC_CMD_RECOVERY_CTRL),
                       .wlength(16'(payload.size())),
                       .payload_bytes(payload),
                       .resp_bytes(response),
                       .label(label));
    endtask

    protected virtual task check_i3c_route_quiescent();
        if (sem_vif.i3c_recovery_payload_available_seen) begin
            `uvm_error("OCP_PAYLOAD_ROUTE",
                "I3C payload-available source was not quiescent across the recovery flow.")
        end
    endtask

    protected virtual task legacy_completion_wait(
        input bit recovery_pending_seen);

        if (recovery_pending_seen) begin
            `uvm_info("OCPREC",
                "DEVICE_STATUS=0x04 RECOVERY_PENDING observed. Holding the main_phase objection so the MCU can complete streaming-boot and report TB_CMD_END_SIM_WITH_SUCCESS (which $finishes the sim). Bounded fail-safe wait engaged.",
                UVM_NONE)
            #200us;
            `uvm_error("OCPREC",
                "Bounded post-RECOVERY_PENDING keep-alive (200us) elapsed without the MCU ending the sim via TB_CMD_END_SIM_WITH_SUCCESS. The streaming-boot handoff did not complete; ending the sequence so the test can report.")
        end
    endtask

    protected virtual task wait_fw_state_generation_bounded(
        input logic [7:0] state,
        input logic [15:0] generation,
        input time timeout,
        input string label,
        input string report_id);

        bit found;

        sem_vif.wait_for_fw_state_generation_bounded(
            state, generation, timeout, found);
        if (!found) begin
            `uvm_fatal(report_id,
                $sformatf("%s firmware state 0x%02h generation %0d timed out.",
                          label, state, generation))
        end
    endtask

    protected virtual task issue_fw_command_and_wait(
        input logic [7:0] command,
        input logic [15:0] generation,
        input logic [7:0] expected_state,
        input time timeout,
        input string label,
        input string report_id);

        sem_vif.issue_fw_command(command, generation);
        wait_fw_state_generation_bounded(
            expected_state, generation, timeout, label, report_id);
        sem_vif.clear_fw_command();
    endtask

    protected virtual task require_recovery_status_pair(
        input ocp_device_status_e expected_device_status,
        input ocp_recovery_status_e expected_recovery_status,
        input bit [3:0] expected_image_index,
        input bit [7:0] expected_vendor_status,
        input ocp_protocol_error_e expected_protocol_error,
        input int unsigned max_polls,
        input time poll_delay,
        input string label,
        input string report_id);

        bit reached;
        bit [7:0] response[$];
        bit [7:0] observed_device_status;
        bit [7:0] observed_protocol_error;
        bit [3:0] observed_recovery_status;
        bit [3:0] observed_image_index;
        bit [7:0] observed_vendor_status;

        poll_device_status(
            expected_device_status, max_polls, poll_delay, reached, response,
            {label, "_DEVICE"});
        observed_device_status =
            (response.size() > OCP_OFF_DS_STATUS) ?
                response[OCP_OFF_DS_STATUS] : 8'hFF;
        observed_protocol_error =
            (response.size() > OCP_OFF_DS_PROT_ERROR) ?
                response[OCP_OFF_DS_PROT_ERROR] : 8'hFF;
        if (!reached ||
            (response.size() < OCP_SPEC_MIN_LEN_DEVICE_STATUS) ||
            (observed_protocol_error != expected_protocol_error)) begin
            `uvm_fatal(report_id,
                $sformatf({"%s DEVICE_STATUS failed: reached=%0b ",
                           "status=0x%02h protocol_error=0x%02h length=%0d."},
                          label, reached, observed_device_status,
                          observed_protocol_error, response.size()))
        end

        poll_recovery_status(
            expected_recovery_status, max_polls, poll_delay, reached, response,
            {label, "_RECOVERY"});
        observed_recovery_status =
            (response.size() > OCP_OFF_RS_STATUS_IMAGE_INDEX) ?
                response[OCP_OFF_RS_STATUS_IMAGE_INDEX][3:0] : 4'hF;
        observed_image_index =
            (response.size() > OCP_OFF_RS_STATUS_IMAGE_INDEX) ?
                response[OCP_OFF_RS_STATUS_IMAGE_INDEX][7:4] : 4'hF;
        observed_vendor_status =
            (response.size() > OCP_OFF_RS_VENDOR_STATUS) ?
                response[OCP_OFF_RS_VENDOR_STATUS] : 8'hFF;
        if (!reached ||
            (response.size() != OCP_SPEC_LEN_RECOVERY_STATUS) ||
            (observed_image_index != expected_image_index) ||
            (observed_vendor_status != expected_vendor_status)) begin
            `uvm_fatal(report_id,
                $sformatf({"%s RECOVERY_STATUS failed: reached=%0b ",
                           "status=0x%01h image_index=%0d vendor=0x%02h ",
                           "length=%0d."},
                          label, reached, observed_recovery_status,
                          observed_image_index, observed_vendor_status,
                          response.size()))
        end
    endtask

    protected virtual task wait_for_recovery_activation_observed(
        input time timeout,
        input time poll_delay,
        input string label,
        input string report_id);

        bit activated;
        int unsigned max_polls;

        activated = 1'b0;
        max_polls = timeout / poll_delay;
        for (int unsigned poll = 0; poll < max_polls; poll++) begin
            if ((sem_vif.recovery_image_activated === 1'b1) ||
                sem_vif.recovery_image_activated_seen) begin
                activated = 1'b1;
                break;
            end
            #(poll_delay);
        end
        if (!activated) begin
            `uvm_fatal(report_id,
                $sformatf("%s recovery activation was not observed.", label))
        end
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

        expected_length = OCP_SPEC_LEN_PROT_CAP;
        if (response.size() != expected_length) begin
            `uvm_error("OCP_BASE",
                $sformatf("PROT_CAP length=%0d, expected %0d per OCP Recovery v1.1 Sec 9.2.",
                          response.size(), expected_length))
        end
        if (response.size() < expected_length) begin
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

    protected virtual task device_id_read_and_check(
        input bit [OCP_SPEC_MIN_LEN_DEVICE_ID*8-1:0] expected_device_id = '0);
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
        if (response.size() == OCP_SPEC_MIN_LEN_DEVICE_ID) begin
            foreach (response[i]) begin
                if (response[i] != expected_device_id[i*8 +: 8]) begin
                    `uvm_error("OCP_BASE",
                        $sformatf("DEVICE_ID byte %0d=0x%02h, expected 0x%02h.",
                                  i, response[i],
                                  expected_device_id[i*8 +: 8]))
                end
            end
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
        input string label,
        input bit stall_expected);

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
        // Synopsys reports STALL-terminated control transfers as ABORTED.
        // Some in-band errors, such as a host write to read-only PROT_CAP,
        // complete successfully while setting PROTOCOL_ERROR.
        if (stall_expected && (result == OCP_XFER_SUCCESS)) begin
            `uvm_error("OCP_BASE",
                $sformatf("%s erroneous transfer completed successfully.",
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

    protected virtual task wait_mcu_axi_idle_before_finish(
        input string label);

        virtual caliptra_ss_usb_legacy_ep0_observer_if observer_vif;
        bit idle;

        if (!uvm_config_db#(
                virtual caliptra_ss_usb_legacy_ep0_observer_if)::get(
                    null, "uvm_test_top.env",
                    "usb_legacy_ep0_observer_if", observer_vif)) begin
            `uvm_fatal("OCP_BASE",
                $sformatf("%s could not obtain the MCU AXI observer.", label))
        end
        observer_vif.wait_for_mcu_axi_idle(100us, idle);
        if (!idle) begin
            `uvm_error("OCP_BASE",
                $sformatf("%s MCU AXI did not reach an idle interval.", label))
        end
    endtask

endclass

`endif // CALIPTRA_SS_USB_OCP_RECOVERY_BASE_SEQUENCE_SV
