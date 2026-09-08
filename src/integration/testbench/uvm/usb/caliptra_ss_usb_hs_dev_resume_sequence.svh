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

        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] body() begin - hub-composite HS resume sequence starting.", UVM_NONE)

        // Start SOF so the link can negotiate HS and reach ENABLED.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_RES_SEQ","SOF generation started.",UVM_LOW)
        end
        `uvm_info("USB_HS_RES_SEQ", "[DBG] Phase: waiting for HS link ENABLED.", UVM_NONE)


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

        // --- Hub-aware enumeration (hub-composite IP) ---
        // The USBDC0 device now sits BEHIND an on-chip 2-port hub. The host
        // must enumerate the HUB itself at addr 1, explicitly bring up its
        // downstream port 1, then enumerate USBDC0 at addr 2. See
        // claude_md/09_usb_hub_composite_migration.md section E and the
        // reference caliptra_ss_usb_hs_dev_bulk_out_sequence.svh.

        // ---------------------------------------------------------------
        // Step A: Enumerate the HUB itself at address 1.
        // ---------------------------------------------------------------
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Step A: enumerating HUB at address 1.", UVM_NONE)
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
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Reconfigured VIP anchor remote device_address=1 (HUB).", UVM_NONE)

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
        // Step B: Bring up downstream port 1 (where USBDC0 is attached).
        // ---------------------------------------------------------------
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Step B: bringing up hub downstream port 1.", UVM_NONE)
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

        // Reset the VIP anchor back to addr=0 before addressing the freshly
        // port-reset USBDC0 (which responds at address 0 like any reset
        // device). Without this the VIP fixed_dev_ep_ustr_valid_ranges
        // constraint (address == anchored 1) contradicts the transfer's WITH
        // constraint (address == 0) and randomize() UVM_FATALs.
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Reset VIP anchor remote device_address=0 before USBDC0 enum.",
            UVM_NONE)

        // ---------------------------------------------------------------
        // Step C: Enumerate USBDC0 (behind hub port 1) at address 2.
        // ---------------------------------------------------------------
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Step C: enumerating USBDC0 at address 2.", UVM_NONE)
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
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Reconfigured VIP anchor remote device_address=2 (USBDC0).",
            UVM_NONE)

        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h06, 16'h0100, 16'h0000, 16'h0012,
            2, "GET_DESC_DEV_addr2", usb_cfg);
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr2");

        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::STANDARD,
            svt_usb_types::BMREQ_DEVICE, 8'h09, 16'h0001, 16'h0000, 16'h0000,
            2, "SET_CONFIG_1", usb_cfg);
        wait_xfer_done(host_agent_h, "SET_CONFIG_1");

        `uvm_info("USB_HS_RES_SEQ","Enumeration done.",UVM_LOW)
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Hub-aware enumeration complete; USBDC0 addressed at 2.",
            UVM_NONE)
        #10us;


        // --- Suspend: stop SOF so device enters suspend state ---
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Phase: SUSPEND - stopping SOF, holding 2500us.", UVM_NONE)
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
        `uvm_info("USB_HS_RES_SEQ",
            $sformatf("[DBG] Phase: RESUME - driving FPR (K) to USBDC0 addr=%0d.",
                usb_cfg.remote_device_cfg[0].device_address), UVM_NONE)
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
            if (shared_status.link_usb_20_state == svt_usb_types::ENABLED) begin
                `uvm_info("USB_HS_RES_SEQ",
                    $sformatf("[DBG] RESUME result: link ENABLED after %0d us poll.",
                        poll_cnt), UVM_NONE)
                `uvm_info("USB_HS_RES_SEQ","Device resumed - link ENABLED.",UVM_LOW)
            end
            else begin
                `uvm_info("USB_HS_RES_SEQ",
                    $sformatf("[DBG] RESUME result: TIMEOUT, link=%0s.",
                        shared_status.link_usb_20_state.name()), UVM_NONE)
                `uvm_error("USB_HS_RES_SEQ",
                    $sformatf("Timeout waiting for ENABLED after FPR; link=%0s",
                        shared_status.link_usb_20_state.name()))
            end
        end
        #100us;
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] body() end - sequence complete.", UVM_NONE)
        `uvm_info("USB_HS_RES_SEQ","caliptra_ss_usb_hs_dev_resume_sequence complete.",UVM_LOW)

    endtask
endclass

`endif // CALIPTRA_SS_USB_HS_DEV_RESUME_SEQUENCE_SV
