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

`ifndef CALIPTRA_SS_USB_FS_HOST_INTNAK_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_HOST_INTNAK_SEQUENCE_SV

// =============================================================================
// USB Full-Speed host interrupt NAK sequence.

// Sequence flow:
//   1. Wait for FS host link to reach ENABLED.
//   2. Start SOF generation.
//   3. Post-reset settling delay for MCU firmware to arm EP0.
//   4. Full enumeration (GET_DESC/GET_STATUS/SET_ADDRESS/GET_DESC/
//      GET_CONFIG/SET_CONFIG/GET_CONFIG verify).
//   5. Send a 4-byte bulk OUT to EP1 (device will NAK since EP1 is not armed).
//   6. Allow observation window for MCU firmware to log result.
// =============================================================================

class caliptra_ss_usb_fs_host_intnak_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_host_intnak_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_fs_host_intnak_sequence");
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

    // -------------------------------------------------------------------------
    // Helper: issue a single CONTROL transfer on p_sequencer.xfer_sequencer.
    // -------------------------------------------------------------------------
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
            `uvm_fatal("USB_FS_INTNAK_SEQ",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_FS_INTNAK_SEQ",
            $sformatf("CONTROL %s done (addr=%0d)", label, device_addr), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Helper: wait for host-side transfer completion.
    // -------------------------------------------------------------------------
    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_FS_INTNAK_SEQ",
            $sformatf("Transfer %s completed on bus.", label), UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        uvm_component         parent_comp;
        svt_configuration     get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      bulk_out_req;
        bit [7:0]             tok_data[];
        int unsigned          i;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_FS_INTNAK_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_FS_INTNAK_SEQ", "get_shared_status returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_FS_INTNAK_SEQ",
                "Unable to cast configuration to svt_usb_configuration")

        // Step 1: Wait for FS link ENABLED.
        `uvm_info("USB_FS_INTNAK_SEQ",
            $sformatf("Waiting for FS host link ENABLED (current=%p)...",
                      shared_status.link_usb_20_state), UVM_LOW)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK;
            end
            begin: REPORT_LINK
                forever begin
                    #10us `uvm_info("USB_FS_INTNAK_SEQ",
                        $sformatf("link_usb_20_state=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_FS_INTNAK_SEQ", "FS host link ENABLED.", UVM_LOW)

        // Step 2: Start SOF generation.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
                "sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_FS_INTNAK_SEQ", "SOF generation started.", UVM_LOW)
        end

        // Step 3: Settling delay.
        #20us;

        // Step 4: Full FS device enumeration.
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

        `uvm_info("USB_FS_INTNAK_SEQ", "FS enumeration complete.", UVM_LOW)
        #10us;

        // Step 5: Attempt bulk OUT to EP1. Device firmware has not armed EP1,
        // so the device will respond with NAK. The host VIP will retry and
        // eventually complete with a NAK-timeout or short transfer status.
        tok_data = new[4];
        tok_data[0] = 8'hAA;
        tok_data[1] = 8'hBB;
        tok_data[2] = 8'hCC;
        tok_data[3] = 8'hDD;

        bulk_out_req = svt_usb_transfer::type_id::create("bulk_out_nak_req");
        start_item(bulk_out_req, -1, p_sequencer.xfer_sequencer);
        bulk_out_req.cfg = usb_cfg;
        bulk_out_req.payload.USER_DEFINED_ALGORITHM_wt   = 1;
        bulk_out_req.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
        bulk_out_req.fix_anchors(0, 1, 0);
        if (!bulk_out_req.randomize() with {
                xfer_type                   == svt_usb_transfer::BULK_OUT_TRANSFER;
                device_address              == 1;
                payload_intended_byte_count == 4;
            }) begin
            `uvm_fatal("USB_FS_INTNAK_SEQ", "Bulk OUT NAK randomize() failed")
        end
        for (i = 0; i < 4; i++) bulk_out_req.payload.data[i] = tok_data[i];
        finish_item(bulk_out_req, -1);
        `uvm_info("USB_FS_INTNAK_SEQ",
            "FS Bulk OUT to unarmed EP1 issued (expect NAK handling).", UVM_LOW)

        // Wait for transfer completion (host will handle NAK and report status).
        wait_xfer_done(host_agent_h, "FS_BULK_OUT_NAK_EP1");

        // Step 6: Observation window for MCU firmware to log result.
        #20us;

        `uvm_info("USB_FS_INTNAK_SEQ",
            "USB FS host interrupt NAK sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_FS_HOST_INTNAK_SEQUENCE_SV
