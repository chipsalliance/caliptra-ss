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

`ifndef CALIPTRA_SS_USB_FS_DEV_BULK_LOOPBACK_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_DEV_BULK_LOOPBACK_SEQUENCE_SV

// =============================================================================
// USB Full-Speed device bulk loopback sequence.
//
// Sequence flow:
//   1. Wait for FS host link to reach ENABLED.
//   2. Issue an explicit USB bus reset (SE0 for tdrst=150us) via the VIP
//      protocol service sequencer. In FS mode with high_speed_capable=0 the
//      SVT VIP host goes directly from attach to ENABLED without driving SE0.
//      The NXP IP_3511HS device controller requires receiving a bus reset to
//      transition from power-on state into DEFAULT state (address=0, EP0 armed,
//      UTMI TX enabled). Without this the DUT never generates ACK or DATA
//      responses and every enumeration transfer ABORTs at the SETUP stage.
//   3. Start SOF generation to keep the FS link alive between transfers.
//   4. Post-reset settling delay for MCU firmware to handle DRES_C and re-arm
//      EP0 buffers.
//   5. Full enumeration (GET_DESC/GET_STATUS/SET_ADDRESS/GET_DESC/
//      GET_CONFIG/SET_CONFIG/GET_CONFIG verify).
//      Each control transfer uses finish_item then a separate wait_xfer_done
//      call -- the same sequential pattern used by the working init and
//      hs_dev_bulk_out sequences. Do NOT fork NOTIFY_USB_TRANSFER_ENDED inside
//      finish_item; the trigger is level-sticky in SVT and wait_trigger works
//      correctly when called after finish_item returns.
//   6. Send 64 bytes of bulk OUT data to EP1 (byte pattern i=0..63).
//      NOTIFY wait is forked BEFORE finish_item for bulk transfers only because
//      a single 64-byte FS packet can complete within the same delta-cycle
//      window as finish_item and the trigger would be missed.
//   7. Read 64 bytes back from EP1 IN (loopback).
//   8. Verify loopback data matches sent bytes.
//   9. Allow MCU firmware time to complete loopback and log result.
// =============================================================================

class caliptra_ss_usb_fs_dev_bulk_loopback_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_dev_bulk_loopback_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_fs_dev_bulk_loopback_sequence");
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
    // Mirrors caliptra_ss_usb_init_sequence and caliptra_ss_usb_hs_dev_bulk_out_sequence:
    // finish_item only inside this task, no NOTIFY wait. The caller must call
    // wait_xfer_done() after this task returns to synchronize with transfer
    // completion on the physical bus.
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
            `uvm_fatal("USB_FS_LOOPBACK_SEQ",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_FS_LOOPBACK_SEQ",
            $sformatf("CONTROL %s issued (addr=%0d).", label, device_addr), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Helper: wait for host-side transfer completion on the physical bus.
    // Called after each do_control_xfer() and after bulk finish_item().
    // -------------------------------------------------------------------------
    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_FS_LOOPBACK_SEQ",
            $sformatf("Transfer %s completed on bus.", label), UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        uvm_component         parent_comp;
        svt_configuration     get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;
        svt_usb_transfer      bulk_out_req;
        svt_usb_transfer      bulk_in_req;
        bit [7:0]             send_data[];
        int unsigned          i;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_FS_LOOPBACK_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_FS_LOOPBACK_SEQ", "get_shared_status returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_FS_LOOPBACK_SEQ",
                "Unable to cast configuration to svt_usb_configuration")

        // Step 1: Wait for FS link ENABLED.
        `uvm_info("USB_FS_LOOPBACK_SEQ",
            $sformatf("Waiting for FS host link ENABLED (current=%p)...",
                      shared_status.link_usb_20_state), UVM_LOW)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK;
            end
            begin: REPORT_LINK
                forever begin
                    #10us `uvm_info("USB_FS_LOOPBACK_SEQ",
                        $sformatf("link_usb_20_state=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_FS_LOOPBACK_SEQ", "FS host link ENABLED.", UVM_LOW)

        // Step 2 (removed): Explicit SE0 bus reset via se0_seq is NOT needed.
        // drive_reset_time is set in the test cfg so the VIP autonomously drives
        // SE0 for 150 us BEFORE transitioning to ENABLED (same as HS mode which
        // drives SE0+chirp mandatorily per USB 2.0 spec). By the time this
        // sequence sees ENABLED the DUT has already received its bus reset.

        // Step 3: Start SOF generation to keep the FS link alive.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
                "sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_FS_LOOPBACK_SEQ", "SOF generation started.", UVM_LOW)
        end

        // Step 4: Post-reset settling delay.
        // Allow MCU firmware time to handle DRES_C interrupt, call
        // usb_handle_bus_reset() / usb_ep0_reinit(), and re-arm EP0 buffers
        // before the first SETUP token arrives on the bus.
        #50us;

        // Step 5: Full FS device enumeration.
        // Pattern matches caliptra_ss_usb_init_sequence and
        // caliptra_ss_usb_hs_dev_bulk_out_sequence: do_control_xfer()
        // calls finish_item; explicit wait_xfer_done() waits for NOTIFY.
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

        `uvm_info("USB_FS_LOOPBACK_SEQ", "FS enumeration complete.", UVM_LOW)
        #10us;

        // Step 6: Send 64 bytes of bulk OUT data to EP1.
        // Data pattern: byte[i] = i (0x00, 0x01, ... 0x3F).
        send_data = new[64];
        for (i = 0; i < 64; i++) send_data[i] = i[7:0];

        bulk_out_req = svt_usb_transfer::type_id::create("bulk_out_req");
        start_item(bulk_out_req, -1, p_sequencer.xfer_sequencer);
        bulk_out_req.cfg = usb_cfg;
        bulk_out_req.payload.USER_DEFINED_ALGORITHM_wt   = 1;
        bulk_out_req.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
        bulk_out_req.fix_anchors(0, 2, 0);
        if (!bulk_out_req.randomize() with {
                xfer_type                              == svt_usb_transfer::BULK_OUT_TRANSFER;
                device_address                         == 1;
                endpoint_number                        == 1;
                payload_intended_byte_count            == 64;
                aligned_transfer_ends_with_zero_length == 0;
            }) begin
            `uvm_fatal("USB_FS_LOOPBACK_SEQ", "Bulk OUT randomize() failed")
        end
        for (i = 0; i < 64; i++) bulk_out_req.payload.data[i] = send_data[i];

        // Fork the NOTIFY wait BEFORE finish_item for bulk transfers.
        // A single 64-byte FS bulk packet completes very fast; if wait_trigger()
        // is called after finish_item the event may have already fired and the
        // task hangs. This race does not affect control transfers (longer
        // multi-stage DATA+STATUS phases give enough slack for sequential calls).
        fork
            begin
                finish_item(bulk_out_req, -1);
                `uvm_info("USB_FS_LOOPBACK_SEQ",
                    "FS Bulk OUT issued (64 bytes, EP1, addr=1).", UVM_LOW)
            end
            begin
                wait_xfer_done(host_agent_h, "FS_BULK_OUT_EP1");
            end
        join

        // Allow MCU firmware time to copy EP1 OUT data to EP1 IN buffer and arm IN.
        #20us;

        // Step 7: Read 64 bytes back from EP1 IN (loopback).
        bulk_in_req = svt_usb_transfer::type_id::create("bulk_in_req");
        start_item(bulk_in_req, -1, p_sequencer.xfer_sequencer);
        bulk_in_req.cfg = usb_cfg;
        bulk_in_req.fix_anchors(0, 1, 0);
        if (!bulk_in_req.randomize() with {
                xfer_type                   == svt_usb_transfer::BULK_IN_TRANSFER;
                device_address              == 1;
                endpoint_number             == 1;
                payload_intended_byte_count == 64;
            }) begin
            `uvm_fatal("USB_FS_LOOPBACK_SEQ", "Bulk IN randomize() failed")
        end

        fork
            begin
                finish_item(bulk_in_req, -1);
                `uvm_info("USB_FS_LOOPBACK_SEQ",
                    "FS Bulk IN issued (64 bytes, EP1, addr=1).", UVM_LOW)
            end
            begin
                wait_xfer_done(host_agent_h, "FS_BULK_IN_EP1");
            end
        join

        // Step 8: Verify loopback data content.
        begin
            int mismatch_count;
            mismatch_count = 0;
            for (int unsigned bi = 0; bi < 64; bi++) begin
                if (bulk_in_req.payload.data[bi] !== send_data[bi]) begin
                    `uvm_error("USB_FS_LOOPBACK_SEQ",
                        $sformatf("Loopback mismatch at byte[%0d]: sent=0x%02h received=0x%02h",
                                  bi, send_data[bi], bulk_in_req.payload.data[bi]))
                    mismatch_count++;
                end
            end
            if (mismatch_count == 0)
                `uvm_info("USB_FS_LOOPBACK_SEQ",
                    "Loopback data check PASSED: all 64 bytes match.", UVM_LOW)
            else
                `uvm_error("USB_FS_LOOPBACK_SEQ",
                    $sformatf("Loopback data check FAILED: %0d byte(s) mismatched.",
                              mismatch_count))
        end

        // Allow MCU firmware time to complete and log result.
        #20us;

        `uvm_info("USB_FS_LOOPBACK_SEQ",
            "USB FS device bulk loopback sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_FS_DEV_BULK_LOOPBACK_SEQUENCE_SV
