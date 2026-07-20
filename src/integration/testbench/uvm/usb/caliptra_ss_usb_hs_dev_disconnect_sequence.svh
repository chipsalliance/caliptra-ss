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

`ifndef CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV

// =============================================================================
// USB High-Speed device disconnect/reconnect sequence.
//
// Sequence flow:
//   1. Start SOF (sof_on_sequence on prot_service_sequencer).
//   2. Wait for HS link ENABLED (initial connection + bus reset from VIP).
//   3. Allow MCU firmware to arm EP0 (20 us settle).
//   4. Full USB enumeration: GET_DESCRIPTOR -> SET_ADDRESS -> SET_CONFIGURATION.
//   5. Hold USB_HS_DISC_SOF_COUNT SOF intervals so MCU can count FRAME_INT events.
//   6. Disconnect: sof_off_sequence (prot_service_sequencer) + vbus_off
//      (p_sequencer.usb_20_phys_service_sequencer).
//   7. Wait for link to leave ENABLED (disconnect detected).
//   8. Hold ~6 us off-time.
//   9. Reconnect: vbus_on (p_sequencer.usb_20_phys_service_sequencer) +
//      sof_on_sequence (prot_service_sequencer).
//  10. Wait for HS link to re-establish (ENABLED again).
//  11. Reset VIP anchor to addr=0 + re-enumerate.
//  12. Hold USB_HS_DISC_SOF_COUNT more SOF intervals so MCU counts FRAME_INT.
//  13. Report success.
// =============================================================================

// SOF interval count to hold on each side of the disconnect (must be >= 6 to
// allow the MCU firmware to count all 6 FRAME_INT events).
`define USB_HS_DISC_SOF_COUNT 8

class caliptra_ss_usb_hs_dev_disconnect_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_disconnect_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_disconnect_sequence");
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

    // Issue a single CONTROL transfer on p_sequencer.xfer_sequencer.
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
                queue_and_hold                     == 0;
            }) begin
            `uvm_fatal("USB_HS_DISC_SEQ",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_HS_DISC_SEQ",
            $sformatf("CONTROL %s issued (addr=%0d wValue=0x%04x wLength=0x%04x)",
                      label, device_addr, wvalue, wlength), UVM_LOW)
    endtask

    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_HS_DISC_SEQ",
            $sformatf("Transfer %s completed on bus.", label), UVM_LOW)
    endtask

    virtual task body();
        svt_usb_agent         host_agent_h;
        uvm_component         parent_comp;
        svt_configuration     get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_HS_DISC_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_DISC_SEQ", "get_shared_status returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_HS_DISC_SEQ", "Cannot cast cfg to svt_usb_configuration")

        // -----------------------------------------------------------------
        // Step 1: Start SOF generation (VBUS on + SOF on).
        // -----------------------------------------------------------------
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "SOF generation started.", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 2: Wait for initial HS link ENABLED.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_DISC_SEQ",
                  "Waiting for initial HS link ENABLED...", UVM_LOW)
        fork
            begin: WAIT_INIT
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_INIT;
            end
            begin: REPORT_INIT
                forever begin
                    #10us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("link_state=%p", shared_status.link_usb_20_state),
                        UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DISC_SEQ", "HS link ENABLED (initial connection).", UVM_LOW)

        // -----------------------------------------------------------------
        // Step 3: Allow MCU firmware to arm EP0 before the first SETUP.
        // -----------------------------------------------------------------
        #100us;

        // -----------------------------------------------------------------
        // Step 4: Enumeration - GET_DESCRIPTOR -> SET_ADDRESS -> SET_CONFIGURATION.
        // -----------------------------------------------------------------

        // GET_DESCRIPTOR (device descriptor, 18 bytes) at addr=0.
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
        `uvm_info("USB_HS_DISC_SEQ", "GET_DESCRIPTOR done.", UVM_LOW)

        // SET_ADDRESS to 1 (sent at addr=0).
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
        `uvm_info("USB_HS_DISC_SEQ", "SET_ADDRESS done.", UVM_LOW)

        // Update VIP anchor to addr=1 so SET_CFG satisfies the VIP constraint.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_DISC_SEQ",
                  "Reconfigured host agent with remote device_address=1.", UVM_LOW)

        // SET_CONFIGURATION 1 at addr=1.
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
        `uvm_info("USB_HS_DISC_SEQ", "Enumeration done.", UVM_LOW)
        #500us;

        // -----------------------------------------------------------------
        // Step 5: Hold USB_HS_DISC_SOF_COUNT SOF intervals so the MCU
        // firmware can count 6 FRAME_INT events before disconnect.
        // -----------------------------------------------------------------
        // repeat (`USB_HS_DISC_SOF_COUNT) begin
        //     #1000us;
        //     `uvm_info("USB_HS_DISC_SEQ",
        //               "SOF interval (pre-disconnect) - count ongoing", UVM_LOW)
        // end
        // #1000us;

        // -----------------------------------------------------------------
        // Step 6: Disconnect - SOF off then VBUS off.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_DISC_SEQ",
                  "Driving disconnect (SOF off + VBUS off)...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence sof_off;
            sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
            sof_off.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "SOF off", UVM_LOW)
        end
        begin
            svt_usb_physical_service_vbus_off_sequence vbus_off;
            vbus_off = svt_usb_physical_service_vbus_off_sequence::type_id::create("vbus_off");
            vbus_off.start(p_sequencer.usb_20_phys_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "VBUS off", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 7: Wait for the link to leave ENABLED state (disconnect
        // detected by VIP link state machine).
        // -----------------------------------------------------------------
        fork
            begin: WAIT_DISC
                wait (shared_status.link_usb_20_state != svt_usb_types::ENABLED);
                disable REPORT_DISC;
            end
            begin: REPORT_DISC
                forever begin
                    #5us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("Waiting for link to leave ENABLED: link=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DISC_SEQ", "Link left ENABLED state (disconnected).", UVM_LOW)

        // -----------------------------------------------------------------
        // Step 8: Hold ~6 us off-time (simulation-time equivalent of 6 ms).
        // -----------------------------------------------------------------
        #1000us;

        // -----------------------------------------------------------------
        // Step 9: Reconnect - VBUS on then SOF on.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_DISC_SEQ",
                  "Reconnecting (VBUS on + SOF on)...", UVM_LOW)
        begin
            svt_usb_physical_service_vbus_on_sequence vbus_on;
            vbus_on = svt_usb_physical_service_vbus_on_sequence::type_id::create("vbus_on");
            vbus_on.start(p_sequencer.usb_20_phys_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "VBUS on", UVM_LOW)
        end
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq2;
            sof_on_seq2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq2");
            sof_on_seq2.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DISC_SEQ", "SOF on", UVM_LOW)
        end

        // -----------------------------------------------------------------
        // Step 10: Wait for HS link to re-establish (ENABLED again).
        // -----------------------------------------------------------------
        fork
            begin: WAIT_RECONN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_RECONN;
            end
            begin: REPORT_RECONN
                forever begin
                    #10us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("Waiting for reconnect: link=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DISC_SEQ",
                  "HS link re-established after reconnect.", UVM_LOW)
        #100us;

        // -----------------------------------------------------------------
        // Step 11: Reset VIP anchor to addr=0 and re-enumerate.
        // After a disconnect+reconnect the device is back at addr=0.
        // -----------------------------------------------------------------
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_DISC_SEQ",
                  "Reset host agent remote device_address=0 for re-enumeration.",
                  UVM_LOW)

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),
            .wvalue                (16'h0100),
            .windex                (16'h0000),
            .wlength               (16'h0012),
            .device_addr           (0),
            .label                 ("GET_DESC_DEV_addr0_re"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0_re");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h05),
            .wvalue                (16'h0001),
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (0),
            .label                 ("SET_ADDRESS_1_re"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_ADDRESS_1_re");

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_DISC_SEQ",
                  "Reconfigured host agent with remote device_address=1 (re-enum).",
                  UVM_LOW)

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h09),
            .wvalue                (16'h0001),
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (1),
            .label                 ("SET_CONFIGURATION_1_re"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_CONFIGURATION_1_re");
        `uvm_info("USB_HS_DISC_SEQ", "Re-enumeration done.", UVM_LOW)
        #500us;

        // // -----------------------------------------------------------------
        // // Step 12: Hold USB_HS_DISC_SOF_COUNT more SOF intervals so the MCU
        // // firmware can count 6 more FRAME_INT events after reconnect.
        // // -----------------------------------------------------------------
        // repeat (`USB_HS_DISC_SOF_COUNT) begin
        //     #1000us;
        //     `uvm_info("USB_HS_DISC_SEQ",
        //               "SOF interval (post-reconnect) - count ongoing", UVM_LOW)
        // end
        // #10000us;

        #500us;

        // -----------------------------------------------------------------
        // Step 13: Report success.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_DISC_SEQ",
                  "HS disconnect/reconnect sequence complete - all phases done.",
                  UVM_LOW)
    endtask

endclass

`undef USB_HS_DISC_SOF_COUNT

`endif // CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV
