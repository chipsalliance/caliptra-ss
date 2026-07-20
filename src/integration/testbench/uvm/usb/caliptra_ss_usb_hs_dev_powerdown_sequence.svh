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

`ifndef CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV

// =============================================================================
// USB HS device power-down sequence.
// Starts SOF, waits for HS link ENABLED, performs standard USB enumeration
// (GET_DESCRIPTOR / SET_ADDRESS / SET_CONFIGURATION), then removes VBUS
// (power-down) and verifies the link leaves ENABLED. VBUS is then restored
// and the link is expected to re-establish (ENABLED again).
// =============================================================================
class caliptra_ss_usb_hs_dev_powerdown_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_powerdown_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_powerdown_sequence");
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
    // Parameter names match caliptra_ss_usb_hs_dev_resume_sequence.
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
        // fix_anchors(dev_idx, ep_idx, upstream_idx): dev_idx is the array
        // index into remote_device_cfg[], always 0 for a single-device setup.
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
            `uvm_fatal("USB_HS_PWRDN_SEQ",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_HS_PWRDN_SEQ",
            $sformatf("CONTROL %s issued (addr=%0d wValue=0x%04x wLength=0x%04x)",
                      label, device_addr, wvalue, wlength), UVM_LOW)
    endtask

    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_HS_PWRDN_SEQ",
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
            `uvm_fatal("USB_HS_PWRDN_SEQ","Cannot cast p_sequencer parent to svt_usb_agent")

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_PWRDN_SEQ","get_shared_status returned null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_HS_PWRDN_SEQ","Cannot cast cfg to svt_usb_configuration")

        // Start SOF so the link can negotiate HS and reach ENABLED.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_PWRDN_SEQ","SOF generation started.",UVM_LOW)
        end

        // Wait for HS link ENABLED.
        fork
            begin: WAIT_EN
                wait(shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK_STATE;
            end
            begin: REPORT_LINK_STATE
                forever begin
                    #10us `uvm_info("USB_HS_PWRDN_SEQ",
                        $sformatf("link=%p", shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_PWRDN_SEQ","HS link ENABLED.",UVM_LOW)

        // Allow MCU firmware to finish initial EP0 arming before the first SETUP.
        #20us;

        // --- Enumeration ---

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

        // SET_ADDRESS to 1 (still at addr=0).
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

        // Update VIP anchor to addr=1 so SET_CFG satisfies the VIP constraint
        // fixed_dev_ep_ustr_valid_ranges (device_address == dev_anchor).
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ","Reconfigured host agent with remote device_address=1.",UVM_LOW)

        // SET_CONFIGURATION 1 at new addr=1.
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
        `uvm_info("USB_HS_PWRDN_SEQ","Enumeration done.",UVM_LOW)
        #500us;

        // --- Power down: stop SOF first, then remove VBUS ---
        // SOF_OFF stops the host from sending SOF packets (bus goes idle).
        // VBUS_OFF removes VBUS via the physical service sequencer.
        // Both are required for a proper power-down.
        `uvm_info("USB_HS_PWRDN_SEQ","Powering down (SOF off + VBUS off)...",UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence sof_off;
            sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
            sof_off.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_PWRDN_SEQ","SOF off",UVM_LOW)
        end
        begin
            svt_usb_physical_service_vbus_off_sequence vbus_off;
            vbus_off = svt_usb_physical_service_vbus_off_sequence::type_id::create("vbus_off");
            vbus_off.start(p_sequencer.usb_20_phys_service_sequencer);
            `uvm_info("USB_HS_PWRDN_SEQ","VBUS off",UVM_LOW)
        end

        // Wait for link to leave ENABLED.
        fork
            begin: WAIT_DOWN
                wait(shared_status.link_usb_20_state != svt_usb_types::ENABLED);
                disable REPORT_DOWN;
            end
            begin: REPORT_DOWN
                forever begin
                    #5us `uvm_info("USB_HS_PWRDN_SEQ",
                        $sformatf("powerdown link=%p", shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_PWRDN_SEQ","Link powered down.",UVM_LOW)
        #1000us;

        // --- Power up: restore VBUS first, then restart SOF ---
        // VBUS_ON re-asserts VBUS; the device will start its attach sequence.
        // SOF_ON restarts SOF generation so the host can negotiate HS and
        // the link state machine can reach ENABLED again.
        `uvm_info("USB_HS_PWRDN_SEQ","Powering up (VBUS on + SOF on)...",UVM_LOW)
        begin
            svt_usb_physical_service_vbus_on_sequence vbus_on;
            vbus_on = svt_usb_physical_service_vbus_on_sequence::type_id::create("vbus_on");
            vbus_on.start(p_sequencer.usb_20_phys_service_sequencer);
        end
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on;
            sof_on = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on");
            sof_on.start(p_sequencer.prot_service_sequencer);
        end

        // Wait for link re-establishment.
        fork
            begin: WAIT_UP
                wait(shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_UP;
            end
            begin: REPORT_UP
                forever begin
                    #10us `uvm_info("USB_HS_PWRDN_SEQ",
                        $sformatf("powerup link=%p", shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_PWRDN_SEQ","HS link re-established after power-up. Test PASSED.",UVM_LOW)
        #500us;

        // Reset VIP anchor back to addr=0 before re-enumeration so that the
        // GET_DESCRIPTOR at addr=0 satisfies the VIP device_address constraint.
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ","Reset host agent remote device_address=0 for re-enumeration.",UVM_LOW)

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

        // SET_ADDRESS to 1 (still at addr=0).
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

        // Update VIP anchor to addr=1 so SET_CFG satisfies the VIP constraint
        // fixed_dev_ep_ustr_valid_ranges (device_address == dev_anchor).
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ","Reconfigured host agent with remote device_address=1.",UVM_LOW)

        // SET_CONFIGURATION 1 at new addr=1.
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
        `uvm_info("USB_HS_PWRDN_SEQ","Enumeration done.",UVM_LOW)
        #500us;
        


    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV
