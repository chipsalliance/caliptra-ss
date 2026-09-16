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

`ifndef CALIPTRA_SS_USB_HS_DEV_RESUME_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_RESUME_SEQUENCE_SV

class caliptra_ss_usb_hs_dev_resume_sequence extends uvm_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_dev_resume_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)
    function new(string name = "caliptra_ss_usb_hs_dev_resume_sequence"); super.new(name); endfunction
    virtual task pre_start();
        uvm_phase phase; super.pre_start(); phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null) phase.raise_objection(this);
    endtask
    virtual task post_start();
        uvm_phase phase; phase = get_starting_phase();
        if (get_parent_sequence() == null && phase != null) phase.drop_objection(this);
    endtask

    // Issue a single CONTROL transfer on p_sequencer.xfer_sequencer.
    // Parameter names match caliptra_ss_usb_init_sequence so named-port calls work.
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
            `uvm_fatal("USB_HS_RES_SEQ",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_HS_RES_SEQ",
            $sformatf("CONTROL %s issued (addr=%0d wValue=0x%04x wLength=0x%04x)",
                      label, device_addr, wvalue, wlength), UVM_LOW)
    endtask

    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_HS_RES_SEQ",
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
            `uvm_fatal("USB_HS_RES_SEQ","Cannot cast p_sequencer parent to svt_usb_agent")

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_RES_SEQ","get_shared_status null.")

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_HS_RES_SEQ","Cannot cast cfg to svt_usb_configuration")

        // Start SOF so the link can negotiate HS and reach ENABLED.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_RES_SEQ","SOF generation started.",UVM_LOW)
        end

        fork
            begin: WAIT_EN
                wait(shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK_STATE;
            end
            begin: REPORT_LINK_STATE
                forever begin
                    #10us `uvm_info("USB_HS_RES_SEQ",
                        $sformatf("link=%p", shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_RES_SEQ","HS link ENABLED.",UVM_LOW)

        // Allow MCU firmware to finish initial EP0 arming before the first SETUP
        // packet arrives. 20 us matches the settling delay used in hs_dev_nbyte.
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

        // Wait for MCU to finish GET_DESCRIPTOR processing and EP1 initial arming
        // before SET_ADDRESS. Without this gap the MCU is still writing EP1 OUT
        // entries when SET_ADDRESS SETUP arrives, causing STATUS ZLP timeout.

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
        `uvm_info("USB_HS_RES_SEQ","Reconfigured host agent with remote device_address=1.",UVM_LOW)

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
        `uvm_info("USB_HS_RES_SEQ","Enumeration done.",UVM_LOW)
        #10us;

        // --- Suspend: stop SOF so device enters suspend state ---
        `uvm_info("USB_HS_RES_SEQ","Suspending (SOF OFF)...",UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end
        $display("SOF stopped");
        // Hold suspended for at least 2500 us. usb_timers_sf uses a Clk1kHz-based
        // suspend timer (SUSPEND_TIME=1 means DeviceSuspended asserts on the 2nd
        // Clk1kHz tick = 2 ms minimum at 48 MHz). 500 us was too short; DSUS never
        // asserted. 2500 us provides 2 ms for the timer plus 500 us margin.
        #2500us;

        // --- Resume: Force Port Resume (K-state) ---
        // Drive K on the bus via the link service sequencer. This sends the
        // USB_20_CLEAR_PORT_SUSPEND command which causes the VIP host to drive
        // K for the spec-required duration and then end-of-resume signaling.
        // Prerequisites: bus must be in SUSPENDED state.
        `uvm_info("USB_HS_RES_SEQ","Resuming (FPR) - driving K on bus...",UVM_LOW)
        begin
            svt_usb_link_service_clear_suspend_sequence link_resume_seq;
            link_resume_seq = svt_usb_link_service_clear_suspend_sequence::type_id::create("link_resume_seq");
            link_resume_seq.device_address = usb_cfg.remote_device_cfg[0].device_address;
            link_resume_seq.start(p_sequencer.link_service_sequencer);
        end
        $display("FPR resuming done");

        // Restart SOF after FPR. The link_service_clear_suspend sequence drives
        // K and end-of-resume but does NOT restart SOF; without it the VIP link
        // SM re-enters SUSPEND after the keepalive timeout.
        
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq2;
            sof_on_seq2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq2");
            sof_on_seq2.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_RES_SEQ","SOF restarted after resume.",UVM_LOW)
        end

        // Wait for link to return to ENABLED after resume.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::ENABLED && poll_cnt < 1000) begin
                #1us; poll_cnt++;
                `uvm_info("USB_HS_RES_SEQ",
                    $sformatf("Waiting ENABLED: link=%0s cnt=%0d",
                        shared_status.link_usb_20_state.name(), poll_cnt), UVM_HIGH)
            end
            if (shared_status.link_usb_20_state == svt_usb_types::ENABLED)
                `uvm_info("USB_HS_RES_SEQ","Device resumed - link ENABLED.",UVM_LOW)
            else
                `uvm_error("USB_HS_RES_SEQ",
                    $sformatf("Timeout waiting for ENABLED after FPR; link=%0s",
                        shared_status.link_usb_20_state.name()))
        end
        #100us;
        `uvm_info("USB_HS_RES_SEQ","caliptra_ss_usb_hs_dev_resume_sequence complete.",UVM_LOW)
    endtask
endclass

`endif // CALIPTRA_SS_USB_HS_DEV_RESUME_SEQUENCE_SV
