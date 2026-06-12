// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_HS_DEV_BULK_OUT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_BULK_OUT_SEQUENCE_SV

// =============================================================================
// USB High-Speed device bulk OUT sequence.
// Sequence flow:
//   1. Wait for HS host link ENABLED (after HS chirp).
//   2. Start SOF generation.
//   3. Short settling delay for MCU firmware post-reset EP0 re-arm.
//   4. Enumerate DUT device (GET_DESC/GET_STATUS/SET_ADDRESS/GET_DESC/
//      GET_CONFIG/SET_CONFIG/GET_CONFIG_verify).
//   5. Send 4096 bytes of bulk OUT data to EP1 via HS.
//      Pattern: 32-bit words 0x00000000, 0x00000001, ..., 0x000003FF
//      (1024 words x 4 bytes = 4096 bytes), matching original COUNT format.
//   6. Allow MCU firmware time to verify the data.
// =============================================================================

`define USB_HS_DEV_BULK_WORDS 1024

class caliptra_ss_usb_hs_dev_bulk_out_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_bulk_out_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_bulk_out_sequence");
        super.new(name);
    endfunction

    virtual task pre_start();
        uvm_phase phase;
        super.pre_start();
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.raise_objection(this);
    endtask

    virtual task post_start();
        uvm_phase phase;
        phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null)
            phase.drop_objection(this);
    endtask

    task do_control_xfer(
        input bit [7:0]  bm_request_type_dir,
        input bit [7:0]  bm_request_type_type,
        input bit [7:0]  bm_request_type_recip,
        input bit [7:0]  brequest_val,
        input bit [15:0] wvalue,
        input bit [15:0] windex,
        input bit [15:0] wlength,
        input int        device_addr,
        input string     label,
        input svt_usb_configuration usb_cfg = null
    );
        svt_usb_transfer req;
        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);
        if (usb_cfg != null)
            req.cfg = usb_cfg;
        req.fix_anchors(0, 0, 0);
        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == device_addr;
                setup_data_bmrequesttype_dir       == bm_request_type_dir;
                setup_data_bmrequesttype_type      == bm_request_type_type;
                setup_data_bmrequesttype_recipient == bm_request_type_recip;
                setup_data_brequest                == brequest_val;
                setup_data_w_value                 == wvalue;
                setup_data_w_index                 == windex;
                setup_data_w_length                == wlength;
            }) begin
            `uvm_fatal("USB_HS_DEV_BULK_SEQ", $sformatf("randomize failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_HS_DEV_BULK_SEQ",
            $sformatf("CONTROL %s done (addr=%0d)", label, device_addr), UVM_LOW)
    endtask

    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_HS_DEV_BULK_SEQ",
            $sformatf("Transfer %s completed.", label), UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent        host_agent_h;
        uvm_component        parent_comp;
        svt_configuration    get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status       shared_status;
        svt_usb_transfer     bulk_req;
        bit [7:0]            bulk_data[];
        int unsigned         word_val;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_HS_DEV_BULK_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_DEV_BULK_SEQ", "get_shared_status returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_HS_DEV_BULK_SEQ", "Unable to cast cfg to svt_usb_configuration")

        // Step 1: Wait for HS link ENABLED.
        `uvm_info("USB_HS_DEV_BULK_SEQ",
            $sformatf("Waiting for HS host link ENABLED (current=%p)...",
                      shared_status.link_usb_20_state), UVM_LOW)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK;
            end
            begin: REPORT_LINK
                forever begin
                    #10us `uvm_info("USB_HS_DEV_BULK_SEQ",
                        $sformatf("link_usb_20_state=%p", shared_status.link_usb_20_state),
                        UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DEV_BULK_SEQ", "HS link ENABLED.", UVM_LOW)

        // Step 2: Start SOF generation.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DEV_BULK_SEQ", "SOF started.", UVM_LOW)
        end

        // Step 3: Settling delay.
        #20us;

        // Step 4: Enumerate device.
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            0, "GET_DESC_DEV_addr0", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h00, 16'h0000, 16'h0000, 16'h0002,
            0, "GET_STATUS_addr0", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_STATUS_addr0");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h05, 16'h0001, 16'h0000, 16'h0000,
            0, "SET_ADDRESS_1", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_ADDRESS_1");
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            1, "GET_DESC_DEV_addr1", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr1");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            1, "GET_CONFIG_addr1", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_CONFIG_addr1");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h09, 16'h0001, 16'h0000, 16'h0000,
            1, "SET_CONFIG_1", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_CONFIG_1");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            1, "GET_CONFIG_verify", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_CONFIG_verify");

        `uvm_info("USB_HS_DEV_BULK_SEQ", "HS enumeration complete.", UVM_LOW)
        #10us;

        // Step 5: Send 4096 bytes bulk OUT via EP1 (HS, 512-byte packets x 8).
        // Data pattern: word[i] = i for i = 0..1023 (COUNT format from original).
        bulk_data = new[`USB_HS_DEV_BULK_WORDS * 4];
        for (int unsigned w = 0; w < `USB_HS_DEV_BULK_WORDS; w++) begin
            word_val = w;
            bulk_data[w*4 + 0] = word_val[7:0];
            bulk_data[w*4 + 1] = word_val[15:8];
            bulk_data[w*4 + 2] = word_val[23:16];
            bulk_data[w*4 + 3] = word_val[31:24];
        end

        bulk_req = svt_usb_transfer::type_id::create("bulk_out_req");
        start_item(bulk_req, -1, p_sequencer.xfer_sequencer);
        bulk_req.cfg = usb_cfg;
        bulk_req.payload.USER_DEFINED_ALGORITHM_wt   = 1;
        bulk_req.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
        bulk_req.fix_anchors(0, 1, 0);
        if (!bulk_req.randomize() with {
                xfer_type                   == svt_usb_transfer::BULK_OUT_TRANSFER;
                device_address              == 1;
                payload_intended_byte_count == (`USB_HS_DEV_BULK_WORDS * 4);
            }) begin
            `uvm_fatal("USB_HS_DEV_BULK_SEQ", "Bulk OUT randomize() failed")
        end
        for (int unsigned bi = 0; bi < (`USB_HS_DEV_BULK_WORDS * 4); bi++)
            bulk_req.payload.data[bi] = bulk_data[bi];
        finish_item(bulk_req, -1);
        `uvm_info("USB_HS_DEV_BULK_SEQ",
            "HS Bulk OUT issued (4096 bytes, EP1, addr=1).", UVM_LOW)

        wait_xfer_done(host_agent_h, "HS_BULK_OUT_EP1");

        // Step 6: Allow MCU time to verify.
        #20us;

        `uvm_info("USB_HS_DEV_BULK_SEQ", "HS device bulk OUT sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_HS_DEV_BULK_WORDS

`endif // CALIPTRA_SS_USB_HS_DEV_BULK_OUT_SEQUENCE_SV
