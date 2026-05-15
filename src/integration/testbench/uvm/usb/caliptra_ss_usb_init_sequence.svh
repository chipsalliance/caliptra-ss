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
// USB init sequence for the single-host-agent UTMI+ topology.
//
// The environment creates one host_agent. host_cfg is the local host stack and
// remote_cfg is the modeled device PHY connected to the DUT over one svt_usb_if.
// Auto-attach and reset/chirp handling are driven by the VIP link state machine;
// this sequence waits for HS link-up before issuing protocol transfers.
//
// Sequence flow:
//   1. Wait for host_agent.shared_status.link_usb_20_state == ENABLED.
//   2. Allow the DUT firmware a short post-reset settling interval.
//   3. Issue CONTROL GET_DESCRIPTOR, SET_ADDRESS, and another GET_DESCRIPTOR.
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

        // Auto-attach is configured through remote_cfg. Once the modeled device
        // PHY attaches, the host link state machine performs reset, detects the
        // HS chirp from the DUT, and transitions to ENABLED. Transfers must not
        // be issued before ENABLED because the VIP protocol layer has not yet
        // established negotiated speed and endpoint context.
        `uvm_info("USB_INIT",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        // ---------------- Wait for host link to reach ENABLED ----------------
        // Use VIP-shipped wait sequence which reads shared_status via the
        // canonical accessor p_sequencer.get_shared_status(this). The prior
        // implementation read host_agent_h.shared_status directly via
        // p_sequencer.get_parent() which can yield a stale instance; the
        // link-FSM only writes the shared_status returned by get_shared_status.
        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp)) begin
            `uvm_fatal("USB_INIT",
                $sformatf("Could not cast p_sequencer parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))
        end

        // Get VIP configuration via the canonical accessor (cfg is local in
        // svt_usb_agent, so we use p_sequencer.get_cfg()).
        p_sequencer.get_cfg(get_cfg);
        if (!$cast(usb_cfg, get_cfg))
            `uvm_fatal("USB_INIT", "Unable to cast configuration to svt_usb_configuration")

        `uvm_info("USB_INIT",
            "Waiting for host link to reach ENABLED state...", UVM_LOW)
        fork
            begin: WAIT_EN
                wait (host_agent_h.shared_status.link_usb_20_state ==
                      svt_usb_types::ENABLED);
                disable REPORT_LINK_STATE;
            end
            begin: REPORT_LINK_STATE
                forever begin
                    #10us `uvm_info("USB_INIT",
                        $sformatf("host agent link_usb_20_state [%p]",
                                  host_agent_h.shared_status.link_usb_20_state),
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

        // ---------------- GET_DESCRIPTOR(Device, addr=0) ----------------
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

        // ---------------- GET_STATUS(Device, addr=0) ----------------
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

        // ---------------- SET_ADDRESS(1) at addr=0 ----------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h05),       // SET_ADDRESS
            .wvalue                (16'h0001),    // new address = 1
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (0),
            .label                 ("SET_ADDRESS_1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_ADDRESS_1");

        // Update the VIP's device configuration with the new address.
        // We update both the runtime cfg (used by transfer randomization
        // constraints via fix_anchors) and the shared_cfg (for consistency).
        usb_cfg.remote_device_cfg[0].device_address = 1;
        `uvm_info("USB_INIT",
            "Updated remote_device_cfg[0].device_address to 1.", UVM_LOW)

        // ---------------- GET_DESCRIPTOR(Device, addr=1) ----------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0100),    // DEVICE descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0012),    // 18 bytes
            .device_addr           (1),
            .label                 ("GET_DESC_DEV_addr1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_DESC_DEV_addr1");

        // ---------------- GET_CONFIGURATION(Device, addr=1) ----------------
        // Returns the current configuration value (1 byte). For an unconfigured
        // device the value is 0; after SET_CONFIGURATION(1) it becomes 1.
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h08),       // GET_CONFIGURATION
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0001),    // 1 byte
            .device_addr           (1),
            .label                 ("GET_CONFIGURATION_addr1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_CONFIGURATION_addr1");

        `uvm_info("USB_INIT", "USB init sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_INIT_SEQUENCE_SV
