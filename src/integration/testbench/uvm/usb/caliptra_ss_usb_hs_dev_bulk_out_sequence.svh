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
// USB High-Speed device bulk OUT sequence (Hub-Enabled mode).
//
// Sequence flow (matches reference janus_usb_host_bfm.sv hub-aware host
// behavior):
//   1. Wait for HS host link ENABLED (after HS chirp).
//   2. Start SOF generation.
//   3. Short settling delay for MCU firmware post-reset EP0 re-arm.
//   4. Enumerate the HUB itself at address 1 (GET_DESC(8)@0 -> SET_ADDRESS(1)
//      -> GET_DESC(18)/GET_DESC(Cfg,9)/GET_DESC(Cfg,25)/GET_DESC(Hub,9)@1 ->
//      SET_CONFIGURATION(1)), then bring up downstream port 1 (where USBDC0
//      is attached) via hub-class requests (GetPortStatus -> ClearFeature
//      (C_PORT_CONNECTION) -> SetFeature(PORT_RESET) -> ClearFeature
//      (C_PORT_RESET)), then enumerate USBDC0 at address 2 (GET_DESC(8)@0 ->
//      SET_ADDRESS(2) -> GET_DESC(18)/GET_CONFIG/SET_CONFIG/GET_CONFIG@2).
//
//      ROOT CAUSE OF device_response_timeout_check_Dev1_EP0: earlier
//      revisions of this sequence tried to address USBDC0 directly as
//      "device 1" (SET_ADDRESS(1) issued straight after GET_STATUS@addr0,
//      with no hub enumeration/port bring-up at all). Since Hub-Enabled
//      mode is active (firmware sets HUB_EN/HUB_CONNECT), the hub entity
//      itself answers at address 0 pre-enumeration and must be enumerated
//      and have its downstream port explicitly brought up (SetFeature
//      (PORT_RESET) etc.) before the hub HW will ever forward SETUP
//      traffic to USBDC0. Skipping this left USBDC0 completely unreachable
//      -> host_agent.prot device_response_timeout on every subsequent
//      transfer nominally addressed to "device 1".
//   5. Send 2048 bytes of bulk OUT data to EP1 via HS (device address 2,
//      i.e. USBDC0 post hub-bring-up).
//      Pattern: 32-bit words 0x00000000, 0x00000001, ..., 0x000001FF
//      (512 words x 4 bytes = 2048 bytes, 4 x 512-byte HS bulk packets).
//      Capped at 2048 B so the EP1 buffer (SRAM offset 0x200..0x9FF) fits
//      within the 4096-byte USB SRAM (addr bus is only 9 bits wide).
//   6. Allow MCU firmware time to verify the data.
// =============================================================================

`define USB_HS_DEV_BULK_WORDS 512

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

        // ---------------------------------------------------------------
        // Step 4a: Enumerate the HUB itself at address 1.
        // ---------------------------------------------------------------
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0008,
            0, "GET_DESC_DEV_addr0_hub", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0_hub");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h05, 16'h0001, 16'h0000, 16'h0000,
            0, "SET_ADDRESS_1_hub", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_ADDRESS_1_hub");
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            1, "GET_DESC_DEV_addr1_hub", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr1_hub");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0200, 16'h0000, 16'h0009,
            1, "GET_DESC_CFG9_addr1_hub", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_CFG9_addr1_hub");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0200, 16'h0000, 16'h0019,
            1, "GET_DESC_CFG25_addr1_hub", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_CFG25_addr1_hub");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h2900, 16'h0000, 16'h0009,
            1, "GET_DESC_HUB9_addr1_hub", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_HUB9_addr1_hub");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h09, 16'h0001, 16'h0000, 16'h0000,
            1, "SET_CONFIG_1_hub", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_CONFIG_1_hub");

        // ---------------------------------------------------------------
        // Step 4b: Bring up downstream port 1 (where USBDC0 is attached).
        // ---------------------------------------------------------------
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h00, 16'h0000, 16'h0001, 16'h0004,
            1, "GetPortStatus_Port1", usb_cfg);
        wait_xfer_done(host_agent_h, "GetPortStatus_Port1");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h01, 16'h0010, 16'h0001, 16'h0000,
            1, "ClearFeature_C_PORT_CONNECTION_Port1", usb_cfg);
        wait_xfer_done(host_agent_h, "ClearFeature_C_PORT_CONNECTION_Port1");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h03, 16'h0004, 16'h0001, 16'h0000,
            1, "SetFeature_PORT_RESET_Port1", usb_cfg);
        wait_xfer_done(host_agent_h, "SetFeature_PORT_RESET_Port1");
        #10us;

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h01, 16'h0014, 16'h0001, 16'h0000,
            1, "ClearFeature_C_PORT_RESET_Port1", usb_cfg);
        wait_xfer_done(host_agent_h, "ClearFeature_C_PORT_RESET_Port1");
        #10us;

        // Reset VIP anchor back to addr=0 before addressing the freshly
        // port-reset USBDC0. The HUB enumeration (Step 4a) left
        // usb_cfg.remote_device_cfg[0].device_address (and the VIP's
        // internal dev_anchor state) at 1. USBDC0, having just been reset
        // via SetFeature(PORT_RESET)/ClearFeature(C_PORT_RESET) on
        // downstream port 1, responds at address 0 like any freshly-reset
        // USB device. Without this reconfigure(), the VIP's own
        // fixed_dev_ep_ustr_valid_ranges constraint (device_address ==
        // dev_anchor.device_address == 1) contradicts the do_control_xfer()
        // WITH_CONSTRAINT (device_address == device_addr == 0), causing a
        // constraint-solver inconsistency (UVM_FATAL) on the very next
        // randomize() call. See caliptra_ss_usb_hs_dev_powerdown_sequence.svh
        // for the equivalent reference pattern.
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_DEV_BULK_SEQ",
            "Reset host agent remote device_address=0 before enumerating USBDC0.",
            UVM_LOW)

        // ---------------------------------------------------------------
        // Step 4c: Enumerate USBDC0 (behind hub port 1) at address 2.
        // ---------------------------------------------------------------
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            0, "GET_DESC_DEV_addr0", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h00, 16'h0000, 16'h0000, 16'h0002,
            0, "GET_STATUS_addr0", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_STATUS_addr0");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h05, 16'h0002, 16'h0000, 16'h0000,
            0, "SET_ADDRESS_2", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_ADDRESS_2");
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd2;
        host_agent_h.reconfigure(usb_cfg);

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            2, "GET_DESC_DEV_addr2", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr2");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            2, "GET_CONFIG_addr2", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_CONFIG_addr2");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h09, 16'h0001, 16'h0000, 16'h0000,
            2, "SET_CONFIG_1", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_CONFIG_1");

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h08, 16'h0000, 16'h0000, 16'h0001,
            2, "GET_CONFIG_verify", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_CONFIG_verify");

        `uvm_info("USB_HS_DEV_BULK_SEQ", "HS enumeration complete.", UVM_LOW)
        #10us;

        // Step 5: Send 2048 bytes bulk OUT via EP1 (HS, 512-byte packets x 4)
        // to USBDC0 at address 2.
        // Data pattern: word[i] = i for i = 0..511 (COUNT format from original).
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
                xfer_type                              == svt_usb_transfer::BULK_OUT_TRANSFER;
                device_address                         == 2;
                endpoint_number                        == 1;
                payload_intended_byte_count            == (`USB_HS_DEV_BULK_WORDS * 4);
                aligned_transfer_ends_with_zero_length == 0;
            }) begin
            `uvm_fatal("USB_HS_DEV_BULK_SEQ", "Bulk OUT randomize() failed")
        end
        for (int unsigned bi = 0; bi < (`USB_HS_DEV_BULK_WORDS * 4); bi++)
            bulk_req.payload.data[bi] = bulk_data[bi];

        // Fork the NOTIFY_USB_TRANSFER_ENDED wait BEFORE finish_item so the
        // trigger is armed before the VIP drives the transfer onto the bus.
        // For short bulk transfers (few packets) the VIP can complete and fire
        // NOTIFY_USB_TRANSFER_ENDED before the thread resumes after finish_item,
        // causing wait_trigger() to miss the pulse and hang indefinitely.
        // Forking the wait first eliminates the race.
        fork
            begin
                finish_item(bulk_req, -1);
                `uvm_info("USB_HS_DEV_BULK_SEQ",
                    "HS Bulk OUT issued (2048 bytes, EP1, addr=2).", UVM_LOW)
            end
            begin
                wait_xfer_done(host_agent_h, "HS_BULK_OUT_EP1");
            end
        join

        // Step 6: Allow MCU time to verify.
        #50us;

        `uvm_info("USB_HS_DEV_BULK_SEQ", "HS device bulk OUT sequence complete.", UVM_LOW)
    endtask

endclass

`undef USB_HS_DEV_BULK_WORDS

`endif // CALIPTRA_SS_USB_HS_DEV_BULK_OUT_SEQUENCE_SV
