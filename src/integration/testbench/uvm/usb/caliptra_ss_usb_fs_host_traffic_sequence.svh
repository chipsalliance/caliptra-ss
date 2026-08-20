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

`ifndef CALIPTRA_SS_USB_FS_HOST_TRAFFIC_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_HOST_TRAFFIC_SEQUENCE_SV

// =============================================================================
// USB Full-Speed host traffic sequence.

//   - Brought up a USB FS device (USB HS device controller)
//   - Set device address to 1, configured EP1 OUT dQH/dTD via direct register writes
//   - Waited for USBINT (IOC) after the host sent 256 bytes of BULK OUT data
//   - Verified received data: data_val2 starts at 0xFF, incremented before
//     compare => word[k] = 0x100 + k  (k = 0..63, 256 bytes total)
// Sequence flow:
//   1. Wait for host link to reach ENABLED (FS link-up after reset/chirp).
//   2. Start SOF generation to keep the FS link alive.
//   3. Allow a short post-reset settling delay for the MCU firmware to re-arm
//      EP0 after bus reset.
//   4. Enumerate the device:
//        GET_DESCRIPTOR(Device, addr=0)
//        GET_STATUS(Device, addr=0)
//        SET_ADDRESS(1)
//        GET_DESCRIPTOR(Device, addr=1)
//        GET_CONFIGURATION(addr=1)
//        SET_CONFIGURATION(1, addr=1)
//        GET_CONFIGURATION(addr=1) verify
//   5. Send 256 bytes of incrementing bulk OUT data via EP1 to the device.
//      Pattern: 32-bit words 0x100, 0x101, 0x102, ... 0x13F (64 words x 4
//      bytes = 256 bytes). Matches the firmware data-check in
//      caliptra_ss_usb_fs_host_traffic.c and the original mem.txt data pattern.
//   6. Wait for the transfer to complete, then allow the MCU a short window to
//      verify the data and print the result before the test ends.
// The sequence reuses the do_control_xfer / wait_xfer_done helpers from
// caliptra_ss_usb_init_sequence since they are included in the same package.
// =============================================================================

// Number of 32-bit words to send in the bulk OUT transfer.
// 64 words * 4 bytes = 256 bytes (0x100), matching original mem.txt dTD
// TotalBytesToTransfer = 0x00FF (0x100-1) and USB_BULK_TRANSFER_BYTES in firmware.
`define USB_FS_TRAFFIC_BULK_WORDS 64

class caliptra_ss_usb_fs_host_traffic_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_host_traffic_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_fs_host_traffic_sequence");
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
    // Identical pattern to caliptra_ss_usb_init_sequence.do_control_xfer.
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
            `uvm_fatal("USB_FS_TRAFFIC_SEQ",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_FS_TRAFFIC_SEQ",
            $sformatf("CONTROL %s done (addr=%0d wValue=0x%04x wLength=0x%04x)",
                      label, device_addr, wvalue, wlength), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Helper: wait for host-side transfer completion.
    // -------------------------------------------------------------------------
    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_FS_TRAFFIC_SEQ",
            $sformatf("Transfer %s completed on bus.", label), UVM_LOW)
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

        // Resolve parent agent handle.
        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp)) begin
            `uvm_fatal("USB_FS_TRAFFIC_SEQ",
                $sformatf("Cannot cast p_sequencer parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))
        end

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_FS_TRAFFIC_SEQ",
                "p_sequencer.get_shared_status(this) returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_FS_TRAFFIC_SEQ",
                "Unable to cast configuration to svt_usb_configuration")

        // -----------------------------------------------------------------
        // Step 1: Wait for FS link ENABLED.
        // Equivalent to original: @ (negedge output_enable) / posedgeHRESETN
        // wait sequence in na_usb_fs_host_traffic.sv.
        // -----------------------------------------------------------------
        `uvm_info("USB_FS_TRAFFIC_SEQ",
            $sformatf("Waiting for host link ENABLED (current=%p)...",
                      shared_status.link_usb_20_state),
            UVM_LOW)

        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK_STATE;
            end
            begin: REPORT_LINK_STATE
                forever begin
                    #10us `uvm_info("USB_FS_TRAFFIC_SEQ",
                        $sformatf("host agent link_usb_20_state [%p]",
                                  shared_status.link_usb_20_state),
                        UVM_LOW);
                end
            end
        join

        `uvm_info("USB_FS_TRAFFIC_SEQ", "Host link ENABLED.", UVM_LOW)

        // -----------------------------------------------------------------
        // Step 2: Start SOF generation to keep the FS link alive.
        // Equivalent to original: VIP auto-attach after USBCMD[RS] set.
        // -----------------------------------------------------------------
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_FS_TRAFFIC_SEQ", "SOF generation started.", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 3: Settling delay for MCU firmware post-reset EP0 re-arm.
        // Original used: repeat(500) posedgeHCLK + #566us for FS mode check.
        // -----------------------------------------------------------------
        #20us;

        // -----------------------------------------------------------------
        // Step 4: Enumeration control transfers.
        // Host drives standard USB 2.0 control transfers to enumerate the device.
        // -----------------------------------------------------------------

        // GET_DESCRIPTOR(Device, addr=0)
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),
            .wvalue                (16'h0100),
            .windex                (16'h0000),
            .wlength               (16'h0012),
            .device_addr           (0),
            .label                 ("GET_DESC_DEV_addr0"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0");

        // GET_STATUS(Device, addr=0)
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h00),
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0002),
            .device_addr           (0),
            .label                 ("GET_STATUS_addr0"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_STATUS_addr0");

        // SET_ADDRESS(1) at addr=0
        // Original: usb_sb.DataWrite(32'h02000000, IP3528_DEVADDR) - sets addr=1
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h05),
            .wvalue                (16'h0001),
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (0),
            .label                 ("SET_ADDRESS_1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_ADDRESS_1");

        // SET_ADDRESS recovery interval (USB 2.0 sec 9.4.6: up to 2 ms).
        #5us;

        // Update remote device address in configuration.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_FS_TRAFFIC_SEQ",
            "Reconfigured host agent with remote device_address=1.", UVM_LOW)

        // GET_DESCRIPTOR(Device, addr=1)
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),
            .wvalue                (16'h0100),
            .windex                (16'h0000),
            .wlength               (16'h0012),
            .device_addr           (1),
            .label                 ("GET_DESC_DEV_addr1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr1");

        // GET_CONFIGURATION(Device, addr=1)
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h08),
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0001),
            .device_addr           (1),
            .label                 ("GET_CONFIGURATION_addr1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_CONFIGURATION_addr1");

        // SET_CONFIGURATION(1, addr=1)
        // Original: usb_sb.DataWrite(32'h00880088, IP3528_EPCTRL1) - enable EP1
        // + usb_sb.DataWrite(32'h00000002, IP3528_EPPRIME) - prime EP1 OUT
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h09),
            .wvalue                (16'h0001),
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (1),
            .label                 ("SET_CONFIGURATION_1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_CONFIGURATION_1");

        // GET_CONFIGURATION(Device, addr=1) verify
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h08),
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0001),
            .device_addr           (1),
            .label                 ("GET_CONFIGURATION_addr1_verify"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_CONFIGURATION_addr1_verify");

        `uvm_info("USB_FS_TRAFFIC_SEQ", "Enumeration complete.", UVM_LOW)

        // Allow MCU firmware time to arm EP1 OUT after SET_CONFIGURATION.
        #10us;

        // -----------------------------------------------------------------
        // Step 5: Send 256 bytes of bulk OUT data via EP1.
        //
        // Data pattern ported from original na_usb_fs_host_traffic mem.txt:
        //   BUF1 Format=COUNT Start=0x0 (4K page at 0x30000)
        //   BUF2 Format=COUNT Start=0x1 (4K page at 0x31000)
        //   ...
        // data_val2 starts at 0xFF and is incremented before each 4-byte
        // compare, so:
        //   word 0 (offset 0x00) = 0x00000100
        //   word 1 (offset 0x04) = 0x00000101
        //   ...
        //   word 63 (offset 0xFC) = 0x0000013F
        // 64 words * 4 bytes = 256 bytes total.
        // This matches USB_BULK_TRANSFER_BYTES and the expected[] array in
        // caliptra_ss_usb_fs_host_traffic.c.
        // -----------------------------------------------------------------
        bulk_data = new[`USB_FS_TRAFFIC_BULK_WORDS * 4];
        for (int unsigned w = 0; w < `USB_FS_TRAFFIC_BULK_WORDS; w++) begin
            word_val = 32'h100 + w;
            bulk_data[w*4 + 0] = word_val[7:0];
            bulk_data[w*4 + 1] = word_val[15:8];
            bulk_data[w*4 + 2] = word_val[23:16];
            bulk_data[w*4 + 3] = word_val[31:24];
        end

        bulk_req = svt_usb_transfer::type_id::create("bulk_out_req");
        start_item(bulk_req, -1, p_sequencer.xfer_sequencer);
        bulk_req.cfg = usb_cfg;
        // Set payload algorithm before randomize so payload.data[] is sized.
        bulk_req.payload.USER_DEFINED_ALGORITHM_wt   = 1;
        bulk_req.payload.TWO_SEED_BASED_ALGORITHM_wt = 0;
        bulk_req.fix_anchors(0, 1, 0);  // ep_idx=1 -> EP1
        if (!bulk_req.randomize() with {
                xfer_type                   == svt_usb_transfer::BULK_OUT_TRANSFER;
                device_address              == 1;
                payload_intended_byte_count == (`USB_FS_TRAFFIC_BULK_WORDS * 4);
            }) begin
            `uvm_fatal("USB_FS_TRAFFIC_SEQ",
                "Bulk OUT svt_usb_transfer randomize() failed")
        end
        // Overwrite payload bytes with the deterministic pattern after randomize.
        for (int unsigned bi = 0; bi < (`USB_FS_TRAFFIC_BULK_WORDS * 4); bi++)
            bulk_req.payload.data[bi] = bulk_data[bi];
        finish_item(bulk_req, -1);
        `uvm_info("USB_FS_TRAFFIC_SEQ",
            "Bulk OUT transfer issued (256 bytes, EP1, addr=1).", UVM_LOW)

        // Original: @ (posedge usb_interrupt) - waits for IOC interrupt.
        // In UVM/SVT: wait for NOTIFY_USB_TRANSFER_ENDED on the host agent.
        wait_xfer_done(host_agent_h, "BULK_OUT_EP1");

        // -----------------------------------------------------------------
        // Step 6: Allow MCU firmware time to verify data and log result.
        // Original: $display + $stop after data_check assertion loop.
        // -----------------------------------------------------------------
        #20us;

        `uvm_info("USB_FS_TRAFFIC_SEQ",
            "USB FS host traffic sequence complete.", UVM_LOW)

    endtask

endclass

`undef USB_FS_TRAFFIC_BULK_WORDS

`endif // CALIPTRA_SS_USB_FS_HOST_TRAFFIC_SEQUENCE_SV
