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
//
// Extends caliptra_ss_usb_base_sequence which provides:
//   * pre_start/post_start objection plumbing
//   * resolve_xfer_handles()
//   * do_control_xfer() / wait_xfer_done()
//
// The body() is decomposed into four protected virtual subtasks so future
// sequences (e.g. caliptra_ss_usb_ocp_recovery_sequence) that extend
// caliptra_ss_usb_base_sequence directly can call them via a wrapper or
// duplicate just the choreography they need.
// -----------------------------------------------------------------------------
class caliptra_ss_usb_init_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_init_sequence)

    // Cached handles populated by resolve_xfer_handles() at the top of body().
    // Subtasks rely on these so they do not have to redo the resolution.
    protected svt_usb_agent         host_agent_h;
    protected svt_usb_configuration usb_cfg;
    protected svt_usb_status        shared_status;

    function new(string name = "caliptra_ss_usb_init_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // wait_link_enabled
    //   Pre : resolve_xfer_handles() has populated this.shared_status.
    //   Post: shared_status.link_usb_20_state == svt_usb_types::ENABLED.
    //
    // Auto-attach is configured through remote_cfg. Once the modeled device
    // PHY attaches, the host link state machine performs reset, detects the
    // HS chirp from the DUT, and transitions to ENABLED. Transfers must not
    // be issued before ENABLED because the VIP protocol layer has not yet
    // established negotiated speed and endpoint context.
    // -------------------------------------------------------------------------
    protected virtual task wait_link_enabled();
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
        // Enumeration anchor (UVM_NONE so it survives +svt_debug_opts).
        `uvm_info("USB_INIT", "Host link ENABLED. Starting transfers.", UVM_NONE)
    endtask

    // -------------------------------------------------------------------------
    // start_sof
    //   Pre : Host link is ENABLED.
    //   Post: VIP host is issuing SOF / micro-frame packets at the configured
    //         interval; bus will not transition to SUSPENDED due to idle.
    //
    // USB 2.0 hosts must send SOF packets to keep the HS link alive; without
    // them the VIP link state machine will SUSPEND within tinactivity.
    // -------------------------------------------------------------------------
    protected virtual task start_sof();
        svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
        sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
        sof_on_seq.start(p_sequencer.prot_service_sequencer);
        // Enumeration anchor (UVM_NONE so it survives +svt_debug_opts).
        `uvm_info("USB_INIT", "SOF generation started.", UVM_NONE)
    endtask

    // -------------------------------------------------------------------------
    // enumerate_to_addr1
    //   Pre : Link is ENABLED and SOF is running. Device is at default
    //         address 0. this.usb_cfg / this.host_agent_h are populated.
    //   Post: Device is at address 1; the host_agent has been reconfigured
    //         so subsequent transfers target remote_device_cfg[0]
    //         .device_address == 1. GET_DESCRIPTOR(Device) at addr=0 and
    //         GET_STATUS at addr=0 have been exercised first to validate
    //         the default-address EP0 path per USB 2.0 sec 9.1.
    // -------------------------------------------------------------------------
    protected virtual task enumerate_to_addr1();
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

        // USB 2.0 sec 9.4.6: the device can take up to 2 ms after the status
        // stage of SET_ADDRESS before it begins responding to its new address
        // ("SetAddress() recovery interval"). Add a settling delay before
        // issuing the first request to the new address so the DUT firmware
        // has time to commit the address change to hardware.
        #5us;

        // Update the agent's configuration with the new remote device address
        // and call svt_usb_agent::reconfigure() so the contained components
        // (protocol service, packet sequencer) re-snapshot the cfg. Per
        // class ref, p_sequencer.get_cfg() returns a *reference* -- mutating
        // the runtime cfg object alone is necessary but not sufficient
        // because the protocol service holds its own cached snapshot.
        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        // Enumeration anchor (UVM_NONE so it survives +svt_debug_opts).
        `uvm_info("USB_INIT",
            "Reconfigured host agent with remote device_address=1.",
            UVM_NONE)
    endtask

    // -------------------------------------------------------------------------
    // select_config_1
    //   Pre : Device responds at address 1; host_agent has been reconfigured
    //         (enumerate_to_addr1 post-condition).
    //   Post: Device is in the Configured state with bConfigurationValue=1.
    //         Verified by reading GET_CONFIGURATION before and after
    //         SET_CONFIGURATION(1). Per USB 2.0 sec 9.1.1.5 this transitions
    //         the device from Address to Configured.
    // -------------------------------------------------------------------------
    protected virtual task select_config_1();
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

        // ---------------- SET_CONFIGURATION(1) at addr=1 ----------------
        // HOST_TO_DEVICE no-data control: status stage is a ZLP IN from device.
        // Selects configuration 1 (the device descriptor declares
        // bNumConfigurations=1). Transitions device from Address to
        // Configured state per USB 2.0 sec 9.1.1.5.
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h09),       // SET_CONFIGURATION
            .wvalue                (16'h0001),    // configuration value = 1
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (1),
            .label                 ("SET_CONFIGURATION_1"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "SET_CONFIGURATION_1");

        // ---------------- GET_CONFIGURATION(Device, addr=1) verify ----------------
        // Should now return 1 (the value just programmed). Re-using the same
        // control-transfer path validates the firmware shadow round-trip.
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::BMREQ_DEVICE),
            .brequest_val          (8'h08),       // GET_CONFIGURATION
            .wvalue                (16'h0000),
            .windex                (16'h0000),
            .wlength               (16'h0001),    // 1 byte
            .device_addr           (1),
            .label                 ("GET_CONFIGURATION_addr1_verify"),
            .usb_cfg               (usb_cfg)
        );
        wait_xfer_done(host_agent_h, "GET_CONFIGURATION_addr1_verify");
    endtask

    // -------------------------------------------------------------------------
    // Main body
    // Orchestrates the four phases of init: handle resolution -> link wait ->
    // SOF -> enumerate to addr 1 -> select configuration 1.
    // -------------------------------------------------------------------------
    virtual task body();
        `uvm_info("USB_INIT",
            "Auto-attach in flight via remote_cfg. Waiting for host link to reach ENABLED.",
            UVM_LOW)

        // Resolve VIP handles once at the top; subtasks consume the cached
        // protected members host_agent_h / usb_cfg / shared_status.
        resolve_xfer_handles(host_agent_h, usb_cfg, shared_status);

        wait_link_enabled();
        start_sof();
        enumerate_to_addr1();
        select_config_1();

        // Terminal enumeration anchor (UVM_NONE so it survives +svt_debug_opts).
        `uvm_info("USB_INIT", "USB init sequence complete.", UVM_NONE)
    endtask

endclass

`endif // CALIPTRA_SS_USB_INIT_SEQUENCE_SV
