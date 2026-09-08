// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_INIT_SEQUENCE_SV
`define CALIPTRA_SS_USB_INIT_SEQUENCE_SV

// =============================================================================
// USB init sequence for the hub-composite topology (single host_agent, UTMI+).
//
// The environment creates one host_agent. host_cfg is the local host stack and
// remote_cfg is the modeled device PHY connected to the DUT over one svt_usb_if.
// Auto-attach and reset/chirp handling are driven by the VIP link state machine;
// this sequence waits for HS link-up before issuing protocol transfers.
//
// The DUT is a USB hub-composite IP: an on-chip 2-port hub with an embedded
// downstream device controller (USBDC0, the MCU-owned DUT device). USBDC0
// sits BEHIND the hub, not directly on the bus. Firmware brings the hub up
// (HUB RAM programming, HUB_EN, then HUB_CONNECT); the host must enumerate
// the hub itself before it can ever see USBDC0, then must explicitly reset/
// enable the hub's downstream port before the hub forwards any SETUP
// traffic to USBDC0.
//
// Sequence flow (see claude_md/09_usb_hub_composite_migration.md Section E):
//   1. Wait for host_agent.shared_status.link_usb_20_state == ENABLED.
//   2. Start SOF generation; allow the DUT firmware a short post-reset
//      settling interval.
//   3. Step 4a - enumerate the HUB itself at address 1 (device + config +
//      hub-class descriptors, SET_CONFIGURATION).
//   4. Step 4b - bring up hub downstream port 1 (where USBDC0 is attached)
//      via hub-class GetPortStatus / ClearFeature(C_PORT_CONNECTION) /
//      SetFeature(PORT_RESET) / ClearFeature(C_PORT_RESET), then reset the
//      VIP's remote device_address anchor back to 0 (USBDC0 answers at
//      address 0 immediately after its port reset, like any freshly-reset
//      device).
//   5. Step 4c - enumerate USBDC0 (behind hub port 1) at address 2:
//      GET_DESCRIPTOR/GET_STATUS/SET_ADDRESS/GET_CONFIGURATION/
//      SET_CONFIGURATION/GET_CONFIGURATION (verify).
//
// This sequence is deliberately minimal (control-plane / enumeration only -
// no data-endpoint traffic, no suspend, no disconnect): it is the smallest,
// fastest smoke test proving boot + EP0 bring-up + enumeration through the
// hub, and the reference device event loop the other USB device tests were
// derived from. Do not grow it into another bulk/data test.
// =============================================================================


// -----------------------------------------------------------------------------
// Optional USB 2.0 port-reset helper. The basic init sequence relies on VIP
// auto-attach/reset, but this helper is kept for tests that need an explicit
// reset after the link is already attached or enabled.
//
// Pattern derived from the canonical UTMI PHY example at
//   $VIPROOT/examples/sverilog/tb_usb_svt_uvm_20_phy/env/pulse_reset_sequence.sv
//
// Drives an svt_usb_link_service item with:
//   service_type         == LINK_20_PORT_COMMAND
//   link_20_command_type == USB_20_PORT_RESET
// on the host agent's link_service_sequencer, accessed through the
// virtual sequencer (p_sequencer.link_service_sequencer).
// -----------------------------------------------------------------------------
class caliptra_ss_usb_port_reset_sequence
    extends svt_usb_link_service_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_port_reset_sequence)

    rand svt_usb_types::link20sm_state_enum link20sm_state_value =
        svt_usb_types::DEVICE_ATTACHED;

    constraint c_link20sm_state {
        link20sm_state_value inside {
            svt_usb_types::DEVICE_ATTACHED,
            svt_usb_types::ENABLED
        };
    }

    function new(string name = "caliptra_ss_usb_port_reset_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_link_service req;
        super.body();
        req = svt_usb_link_service::type_id::create("req");
        start_item(req);
        if (!req.randomize() with {
                service_type               == svt_usb_link_service::LINK_20_PORT_COMMAND;
                link_20_command_type       == svt_usb_link_service::USB_20_PORT_RESET;
                prereq_link_20_state       == link20sm_state_value;
                link_service_delay_longint == 0;
                prereq_ltssm_delay_longint == 0;
            }) begin
            `uvm_fatal("USB_INIT", "USB_20_PORT_RESET link-service randomize() failed")
        end
        finish_item(req);
        `uvm_info("USB_INIT",
            "USB_20_PORT_RESET link service issued",
            UVM_LOW)
    endtask

endclass

// -----------------------------------------------------------------------------
// Top-level init sequence (started on env.host_agent.virt_sequencer).
// -----------------------------------------------------------------------------
class caliptra_ss_usb_init_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_init_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_init_sequence");
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
    //
    // Uses the canonical VIP pattern: set cfg + fix_anchors before randomize
    // (see $VIPROOT examples usb_directed_transfers_sequence.sv).
    // -------------------------------------------------------------------------
    task do_control_xfer(
        input bit [7:0]  bm_request_type_dir,    // svt_usb_types direction enum
        input bit [7:0]  bm_request_type_type,   // svt_usb_types type enum
        input bit [7:0]  bm_request_type_recip,  // svt_usb_types recipient enum
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
        // Set cfg so the transfer's internal constraints can resolve
        // device/endpoint anchors. fix_anchors(dev_idx, ep_idx, upstream_idx)
        // tells the randomizer which remote_device_cfg entry to use.
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
            `uvm_fatal("USB_INIT",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_INIT",
            $sformatf("CONTROL %s done (addr=%0d wValue=0x%04x wLength=0x%04x)",
                      label, device_addr, wvalue, wlength), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Helper: wait for host-side transfer completion.
    //
    // The xfer_sequencer accepts transfers into its pending queue and
    // finish_item returns immediately. The protocol scheduler sends the
    // transfer on the bus asynchronously. We must wait for
    // NOTIFY_USB_TRANSFER_ENDED before proceeding.
    //
    // Pattern from VIP example:
    //   attach_bulk_xfers_detach_hs_sequence.sv (fork/join on
    //   host_agent.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger)
    // -------------------------------------------------------------------------
    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_INIT",
            $sformatf("Transfer %s completed on bus.", label), UVM_LOW)
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        svt_usb_agent host_agent_h;
        uvm_component parent_comp;
        svt_configuration get_cfg;
        svt_usb_configuration usb_cfg;
        svt_usb_status shared_status;

        // Auto-attach is configured through remote_cfg. Once the modeled device
        // PHY attaches, the host link state machine performs reset, detects the
        // HS chirp from the DUT, and transitions to ENABLED. Transfers must not
        // be issued before ENABLED because the VIP protocol layer has not yet
        // established negotiated speed and endpoint context.
        `uvm_info("USB_INIT",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        // ---------------- Resolve VIP handles for wait + transfers ----------------
        // The svt_usb_status object that the link FSM writes is shared between
        // the agent (`host_agent_h.shared_status`) and the canonical accessor
        // (`p_sequencer.get_shared_status(this)`). Empirically verified in
        // pkg125: both return the same object instance (id matches). We use
        // the canonical accessor as the recommended path.
        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp)) begin
            `uvm_fatal("USB_INIT",
                $sformatf("Could not cast p_sequencer parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))
        end

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null) begin
            `uvm_fatal("USB_INIT",
                "p_sequencer.get_shared_status(this) returned null.")
        end

        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_INIT", "Unable to cast configuration to svt_usb_configuration")

        `uvm_info("USB_INIT",
            $sformatf("Waiting for host link to reach ENABLED (current=%p)...",
                      shared_status.link_usb_20_state),
            UVM_LOW)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state ==
                      svt_usb_types::ENABLED);
                disable REPORT_LINK_STATE;
            end
            begin: REPORT_LINK_STATE
                forever begin
                    #10us `uvm_info("USB_INIT",
                        $sformatf("host agent link_usb_20_state [%p]",
                                  shared_status.link_usb_20_state),
                        UVM_LOW);
                end
            end
        join
        `uvm_info("USB_INIT", "Host link ENABLED. Starting transfers.", UVM_LOW)

        // Start SOF (Start of Frame) generation on the host. USB 2.0 hosts
        // must send SOF/micro-frame packets to keep the link alive; without
        // this the VIP link state machine will transition to SUSPENDED
        // within the idle timeout window.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_INIT", "SOF generation started.", UVM_LOW)
        end

        // Small settling delay before issuing the first SETUP transfer so the
        // DUT firmware has had time to handle the bus-reset interrupt
        // (DRES_C) and re-prime EP0.
        #20us;

        // ---------------------------------------------------------------
        // Step 4a: Enumerate the HUB itself at address 1.
        //
        // In Hub-Enabled mode the hub entity answers at address 0 pre-
        // enumeration. USBDC0 is unreachable until the hub is enumerated
        // and its downstream port is explicitly reset/enabled (step 4b).
        // ---------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0100),    // DEVICE descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0008),    // 8 bytes
            .device_addr           (0),
            .label                 ("GET_DESC_DEV_addr0_hub"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0_hub");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h05),       // SET_ADDRESS
            .wvalue                (16'h0001),    // new address = 1
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (0),
            .label                 ("SET_ADDRESS_1_hub"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_ADDRESS_1_hub");

        // USB 2.0 §9.4.6: the device can take up to 2 ms after the status
        // stage of SET_ADDRESS before it begins responding to its new
        // address ("SetAddress() recovery interval"). Settle before the
        // first request to the new address.
        #5us;

        // Mutating the runtime cfg object alone is necessary but not
        // sufficient - the protocol service holds its own cached snapshot,
        // so reconfigure() must be called in lockstep with every
        // SET_ADDRESS (VIP pitfall, claude_md/09 Section E).
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_INIT",
            "Reconfigured host agent with remote device_address=1 (hub).",
            UVM_LOW)

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0100),    // DEVICE descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0012),    // 18 bytes
            .device_addr           (1),
            .label                 ("GET_DESC_DEV_addr1_hub"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr1_hub");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0200),    // CONFIGURATION descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0009),    // 9 bytes (config header only)
            .device_addr           (1),
            .label                 ("GET_DESC_CFG9_addr1_hub"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_CFG9_addr1_hub");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0200),    // CONFIGURATION descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0019),    // 25 bytes (config + interface + EP)
            .device_addr           (1),
            .label                 ("GET_DESC_CFG25_addr1_hub"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_CFG25_addr1_hub");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::CLASS),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h2900),    // Hub class descriptor
            .windex                (16'h0000),
            .wlength               (16'h0009),    // 9 bytes
            .device_addr           (1),
            .label                 ("GET_DESC_HUB9_addr1_hub"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_HUB9_addr1_hub");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h09),       // SET_CONFIGURATION
            .wvalue                (16'h0001),    // configuration value = 1
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (1),
            .label                 ("SET_CONFIG_1_hub"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_CONFIG_1_hub");

        // ---------------------------------------------------------------
        // Step 4b: Bring up downstream port 1 (where USBDC0 is attached).
        //
        // Hub-class requests, recipient BMREQ_OTHER (port). This is
        // mandatory, not optional: the hub hardware will not forward any
        // SETUP to USBDC0 until its downstream port has been enumerated
        // and explicitly reset/enabled.
        // ---------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::CLASS),
            .bm_request_type_recip (svt_usb_types::BMREQ_OTHER),
            .brequest_val          (8'h00),       // GetPortStatus
            .wvalue                (16'h0000),
            .windex                (16'h0001),    // port 1
            .wlength               (16'h0004),    // 4 bytes
            .device_addr           (1),
            .label                 ("GetPortStatus_Port1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GetPortStatus_Port1");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::CLASS),
            .bm_request_type_recip (svt_usb_types::BMREQ_OTHER),
            .brequest_val          (8'h01),       // ClearFeature
            .wvalue                (16'h0010),    // C_PORT_CONNECTION
            .windex                (16'h0001),    // port 1
            .wlength               (16'h0000),
            .device_addr           (1),
            .label                 ("ClearFeature_C_PORT_CONNECTION_Port1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "ClearFeature_C_PORT_CONNECTION_Port1");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::CLASS),
            .bm_request_type_recip (svt_usb_types::BMREQ_OTHER),
            .brequest_val          (8'h03),       // SetFeature
            .wvalue                (16'h0004),    // PORT_RESET
            .windex                (16'h0001),    // port 1
            .wlength               (16'h0000),
            .device_addr           (1),
            .label                 ("SetFeature_PORT_RESET_Port1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SetFeature_PORT_RESET_Port1");
        #10us;

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::CLASS),
            .bm_request_type_recip (svt_usb_types::BMREQ_OTHER),
            .brequest_val          (8'h01),       // ClearFeature
            .wvalue                (16'h0014),    // C_PORT_RESET
            .windex                (16'h0001),    // port 1
            .wlength               (16'h0000),
            .device_addr           (1),
            .label                 ("ClearFeature_C_PORT_RESET_Port1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "ClearFeature_C_PORT_RESET_Port1");
        #10us;

        // Reset the VIP anchor back to addr=0 before addressing the
        // freshly port-reset USBDC0. Step 4a left
        // usb_cfg.remote_device_cfg[0].device_address (and the VIP's
        // internal dev_anchor state) at 1. USBDC0, having just been reset
        // via SetFeature(PORT_RESET)/ClearFeature(C_PORT_RESET) on
        // downstream port 1, responds at address 0 like any freshly-reset
        // USB device. Without this reconfigure(), the VIP's own
        // fixed_dev_ep_ustr_valid_ranges constraint (device_address ==
        // dev_anchor.device_address == 1) contradicts the do_control_xfer()
        // WITH constraint (device_address == device_addr == 0), causing a
        // constraint-solver inconsistency (UVM_FATAL) on the very next
        // randomize() call.
        usb_cfg.remote_device_cfg[0].device_address = 7'd0;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_INIT",
            "Reset host agent remote device_address=0 before enumerating USBDC0.",
            UVM_LOW)

        // ---------------------------------------------------------------
        // Step 4c: Enumerate USBDC0 (behind hub port 1) at address 2.
        // ---------------------------------------------------------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0100),    // DEVICE descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0012),    // 18 bytes
            .device_addr           (0),
            .label                 ("GET_DESC_DEV_addr0"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr0");

        // Standard device GET_STATUS: returns 2-byte status word
        //   bit[0] = Self-Powered, bit[1] = Remote Wakeup (both 0 for this device)
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h00),       // GET_STATUS
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0002),    // 2 bytes
            .device_addr           (0),
            .label                 ("GET_STATUS_addr0"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_STATUS_addr0");

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h05),       // SET_ADDRESS
            .wvalue                (16'h0002),    // new address = 2
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (0),
            .label                 ("SET_ADDRESS_2"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_ADDRESS_2");
        #5us;

        usb_cfg.remote_device_cfg[0].device_address = 7'd2;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_INIT",
            "Reconfigured host agent with remote device_address=2 (USBDC0).",
            UVM_LOW)

        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0100),    // DEVICE descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0012),    // 18 bytes
            .device_addr           (2),
            .label                 ("GET_DESC_DEV_addr2"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr2");

        // Returns the current configuration value (1 byte). For an
        // unconfigured device the value is 0; after SET_CONFIGURATION(1)
        // it becomes 1.
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h08),       // GET_CONFIGURATION
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0001),    // 1 byte
            .device_addr           (2),
            .label                 ("GET_CONFIGURATION_addr2"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_CONFIGURATION_addr2");

        // HOST_TO_DEVICE no-data control: status stage is a ZLP IN from
        // device. Selects configuration 1 (the device descriptor declares
        // bNumConfigurations=1). Transitions device from Address ->
        // Configured state per USB 2.0 Section 9.1.1.5.
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h09),       // SET_CONFIGURATION
            .wvalue                (16'h0001),    // configuration value = 1
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (2),
            .label                 ("SET_CONFIGURATION_addr2"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_CONFIGURATION_addr2");

        // Should now return 1 (the value just programmed). Re-using the
        // same control-transfer path validates the firmware shadow
        // round-trip.
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h08),       // GET_CONFIGURATION
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0001),    // 1 byte
            .device_addr           (2),
            .label                 ("GET_CONFIGURATION_addr2_verify"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_CONFIGURATION_addr2_verify");

        `uvm_info("USB_INIT", "USB init sequence complete (hub + USBDC0 enumerated).", UVM_LOW)
    endtask


endclass

`endif // CALIPTRA_SS_USB_INIT_SEQUENCE_SV
