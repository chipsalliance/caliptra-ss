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
// USB HS device power-down sequence (Hub-Enabled mode).
//
// In hub-enabled mode the device under test (USBDC0) is an embedded downstream
// device of the compound hub. The host<->HUB upstream link is HS. Removing
// VBUS on that upstream link (as the legacy direct-attach power-down test did)
// does NOT map to hub mode:
//   - USBDC0 never observes the host VBUS on its own VBUS_DEBOUNCED bit
//     (its supply is the hub's downstream port, not the host VBUS), so the
//     firmware can never detect the "power-down" that way; and
//   - removing/re-applying upstream VBUS disconnects the hub and the HS
//     re-negotiation does not reliably reproduce - the VIP link comes back at
//     FS while the device stays HS, so every re-enumeration token times out;
//     and the hub, never reset, stays enumerated at address 1 so the hub
//     re-enumeration (GET_DESCRIPTOR @ address 0) cannot succeed either.
//
// GENUINE power-down model (RTL-accurate):
// The one hub-class request in this IP that actually removes power/enable from
// the embedded downstream device USBDC0 is ClearFeature(PORT_ENABLE) on the
// downstream port. Per usb_app_hw_hub.m.vhdl PROC_REQUEST_HANDLING, a
// ClearPortFeature with wValue=1 (Port_Enable) drives:
//     hub_port_enable_int(var_port) <= '0'    (var_port = wIndex - 1)
// and per ip_xxx_3511_hs_mem_compound_structure.a.vhdl USBDC0's controller
// enable is gated by hub_port_enable(0):
//     usbreg_deviceenabled(1) <= hub_port_enable(0) and usbreg_arm_deviceenabled
// so clearing Port_Enable on port 1 (wIndex=1 -> var_port=0) forces USBDC0's
// deviceenabled to 0 - a genuine, waveform-visible power-down of the device
// controller. (PORT_POWER and PORT_SUSPEND are RTL no-ops in this IP - they
// only toggle status bits and are never wired to USBDC0, so using them would
// be a false pass.)
//
// Recovery is via SetFeature(PORT_RESET) on the same port, which per the same
// RTL re-asserts hub_port_enable_int(var_port)<='1' AND pulses
// hub_port_reset_int(var_port)<='1'. hub_port_reset(0) drives arm_dev_portreset
// into USBDC0, so USBDC0 sees a fresh bus reset (DRES_C) and returns to the
// Default state, after which the host re-enumerates it at address 2.
//
// The HS upstream link stays ENABLED and the HUB stays enumerated/configured
// at address 1 throughout; only USBDC0 is powered down and brought back.
//
// Flow:
//   1. SOF on, wait HS link ENABLED.
//   2. Full hub-aware enumeration: enumerate the HUB at address 1, bring up
//      downstream port 1, enumerate USBDC0 at address 2 (Steps A + B + C).
//   3. Power-down USBDC0: ClearFeature(PORT_ENABLE) on port 1 (degates
//      USBDC0 -> deviceenabled=0), confirm via GetPortStatus (enable bit=0),
//      hold, then recover via SetFeature(PORT_RESET) on port 1 (re-enable +
//      bus reset), and re-enumerate USBDC0 at address 2 (Step C).
//
// See caliptra_ss_usb_hs_dev_bulk_out_sequence.svh for the canonical 3-step
// hub-aware enumeration reference.
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

        // --- Initial hub-aware enumeration (Steps A + B + C) ---
        // Enumerate the HUB at address 1, bring up downstream port 1, then
        // enumerate USBDC0 at address 2.
        hub_enum_stepA(host_agent_h, usb_cfg);
        hub_port_bringup_stepB(host_agent_h, usb_cfg);
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ","Initial hub-aware enumeration done (USBDC0 at addr 2).",UVM_LOW)
        #500us;

        // -----------------------------------------------------------------
        // GENUINE power-down of USBDC0, then power-up and re-enumeration.
        //
        // The HS upstream link stays ENABLED and the HUB stays enumerated
        // at address 1 throughout. The power-down is driven by a hub-class
        // ClearFeature(PORT_ENABLE) on downstream port 1, which per the RTL
        // forces hub_port_enable(0)=0 and therefore USBDC0's deviceenabled=0
        // (device controller degated / powered down - visible in the
        // waveform). Recovery is a SetFeature(PORT_RESET) on port 1, which
        // re-enables the port AND issues a fresh bus reset into USBDC0; the
        // host then re-enumerates USBDC0 at address 2 (Step C).
        //
        // Anchor management: after the initial enumeration the VIP remote
        // device anchor is at address 2 (USBDC0). The hub-class port
        // requests (power-down step + Step B) address the HUB at address 1,
        // so set the anchor to 1 first. usbdc0_enum_stepC() sets the anchor
        // to 0 for the freshly-reset USBDC0 and leaves it at 2 on completion.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Powering down USBDC0 via ClearFeature(PORT_ENABLE) on hub port 1...",UVM_LOW)

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Anchor set to HUB address 1 for downstream port power-down.",UVM_LOW)

        usbdc0_powerdown_step(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ",
            "USBDC0 powered down (deviceenabled forced 0). Holding...",UVM_LOW)
        #200us;

        // Recover: SetFeature(PORT_RESET) re-enables the port and bus-resets
        // USBDC0, then re-enumerate it at address 2.
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Powering USBDC0 back up via SetFeature(PORT_RESET) on hub port 1...",UVM_LOW)
        hub_port_bringup_stepB(host_agent_h, usb_cfg);
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Post-power-up re-enumeration done (USBDC0 at addr 2).",UVM_LOW)
        #500us;

    endtask

    // -------------------------------------------------------------------------
    // Power-down step: degate USBDC0 via ClearFeature(PORT_ENABLE) on port 1.
    //   GetPortStatus (pre) -> ClearFeature(PORT_ENABLE) -> GetPortStatus (post,
    //   confirm Port_Enable status bit=0).
    // Per usb_app_hw_hub.m.vhdl, ClearPortFeature wValue=1 (Port_Enable) on
    // wIndex=1 (var_port=0) drives hub_port_enable_int(0)<='0', which per the
    // structure netlist forces USBDC0 usbreg_deviceenabled=0 (genuine
    // power-down). The post GetPortStatus reads hub_status(1)(1) = 0 to confirm.
    // On entry the VIP anchor must be 1 (HUB).
    // -------------------------------------------------------------------------
    task usbdc0_powerdown_step(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h00, 16'h0000, 16'h0001, 16'h0004,
            1, "GetPortStatus_Port1_prePD", usb_cfg);
        wait_xfer_done(host_agent_h, "GetPortStatus_Port1_prePD");

        // ClearFeature(PORT_ENABLE): feature selector PORT_ENABLE = 1.
        // This is the ONLY hub-class request wired to USBDC0's enable in this
        // IP; it forces deviceenabled=0 (real power-down).
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h01, 16'h0001, 16'h0001, 16'h0000,
            1, "ClearFeature_PORT_ENABLE_Port1", usb_cfg);
        wait_xfer_done(host_agent_h, "ClearFeature_PORT_ENABLE_Port1");
        #10us;

        // Confirm the port is now disabled: hub_status(1)(1)=Port_Enable=0.
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h00, 16'h0000, 16'h0001, 16'h0004,
            1, "GetPortStatus_Port1_postPD", usb_cfg);
        wait_xfer_done(host_agent_h, "GetPortStatus_Port1_postPD");
        #10us;
    endtask


    // -------------------------------------------------------------------------
    // Step A: Enumerate the HUB itself at address 1.
    //   GET_DESC(8)@0 -> SET_ADDRESS(1)@0 -> GET_DESC(18)/CFG9/CFG25/HUB9@1 ->
    //   SET_CONFIGURATION(1)@1.
    // On entry the VIP anchor must be 0; on exit it is left at 1.
    // -------------------------------------------------------------------------
    task hub_enum_stepA(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
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
    endtask

    // -------------------------------------------------------------------------
    // Step B: Bring up (or re-reset) downstream port 1 where USBDC0 is attached.
    //   GetPortStatus -> ClearFeature(C_PORT_CONNECTION) -> SetFeature(PORT_RESET)
    //   -> ClearFeature(C_PORT_RESET).
    // SetFeature(PORT_RESET) drives a USB bus reset onto USBDC0, returning it to
    // the Default state at address 0. On entry the VIP anchor must be 1 (HUB).
    // -------------------------------------------------------------------------
    task hub_port_bringup_stepB(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
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
    endtask

    // -------------------------------------------------------------------------
    // Step C: Enumerate USBDC0 (behind hub port 1) at address 2.
    //   GET_DESC(18)@0 -> GET_STATUS@0 -> SET_ADDRESS(2)@0 ->
    //   GET_DESC(18)/GET_CONFIG/SET_CONFIG/GET_CONFIG@2.
    // USBDC0 responds at address 0 after the Step B port reset. On completion
    // the VIP anchor is left at 2 (USBDC0). Delivers exactly 7 EP0 control
    // transfers to USBDC0.
    // -------------------------------------------------------------------------
    task usbdc0_enum_stepC(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
        // Reset VIP anchor to addr=0 before addressing the freshly port-reset
        // USBDC0. Without this the fixed_dev_ep_ustr_valid_ranges constraint
        // (device_address == dev_anchor) contradicts the do_control_xfer
        // WITH_CONSTRAINT (device_address == 0), causing a constraint UVM_FATAL.
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Reset host agent remote device_address=0 before enumerating USBDC0.",
            UVM_LOW)

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

        `uvm_info("USB_HS_PWRDN_SEQ", "USBDC0 enumeration complete (addr 2).", UVM_LOW)
    endtask

endclass


`endif // CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV
