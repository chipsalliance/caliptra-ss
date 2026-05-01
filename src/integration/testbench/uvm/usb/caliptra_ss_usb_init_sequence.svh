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
// USB init sequence: VIP-native enumeration over UTMI.
//
// The Synopsys USB VIP is configured at top_layer = PROTOCOL with
// usb_20_signal_interface = UTMI_IF. In this configuration the VIP itself
// drives all UTMI line-level signaling (J/K/SE0, SOF, tokens, DATA0/1,
// handshakes), so the testbench only needs to issue high-level transactions
// on the VIP sequencers. No manual UTMI byte injection, no force/release
// scaffolding is required (or permitted).
//
// Sequence flow:
//   1. Wait ~200us for the DUT firmware (usb_init.c) to bring up the
//      controller and program EP0.
//   2. Issue a USB 2.0 bus reset via svt_usb_link_service
//      (LINK_20_PORT_COMMAND / SVT_USB_20_PORT_RESET) on the host_agent
//      link-service sequencer, accessed directly via the virtual
//      sequencer's link_service_sequencer handle.
//   3. Wait ~100us for firmware to handle DRES_C and re-init EP0.
//   4. Issue a CONTROL GET_DESCRIPTOR(Device, len=18) using svt_usb_transfer
//      on the xfer_sequencer via the virtual sequencer.
//   5. Issue a CONTROL SET_ADDRESS(1) and a follow-up GET_DESCRIPTOR using
//      the new address to validate enumeration.
// =============================================================================

// -----------------------------------------------------------------------------
// NOTE on bus reset:
//   The VIP host agent at top_layer = PROTOCOL with
//   poweron_auto_attach_delay = 0 automatically drives the bus reset as part
//   of its connect / port-power-up sequence. No explicit svt_usb_link_service
//   item is required for basic enumeration in this VIP release.
//   (The SVT_USB_20_PORT_RESET enum on svt_usb_link_service is only exposed
//   in newer SVT releases and is not used here.)
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// Bus reset sub-sequence: explicit VIP-native USB 2.0 port reset.
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
    // -------------------------------------------------------------------------
    task do_control_xfer(
        input bit [7:0]  bm_request_type_dir,    // svt_usb_types direction enum
        input bit [7:0]  bm_request_type_type,   // svt_usb_types type enum
        input bit [7:0]  bm_request_type_recip,  // svt_usb_types recipient enum
        input bit [7:0]  brequest,
        input bit [15:0] wvalue,
        input bit [15:0] windex,
        input bit [15:0] wlength,
        input int        device_addr,
        input string     label
    );
        svt_usb_transfer req;
        req = svt_usb_transfer::type_id::create({label, "_req"});
        start_item(req, -1, p_sequencer.xfer_sequencer);
        if (!req.randomize() with {
                xfer_type                          == svt_usb_transfer::CONTROL_TRANSFER;
                device_address                     == device_addr;
                setup_data_bmrequesttype_dir       == bm_request_type_dir;
                setup_data_bmrequesttype_type      == bm_request_type_type;
                setup_data_bmrequesttype_recipient == bm_request_type_recip;
                setup_data_brequest                == brequest;
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
    // Main body
    // -------------------------------------------------------------------------
    virtual task body();
        caliptra_ss_usb_port_reset_sequence rst_seq;

        `uvm_info("USB_INIT",
            "Waiting ~200us for DUT firmware USB controller bring-up...",
            UVM_LOW)
        #200us;

        // ---------------- Explicit USB 2.0 Bus reset ----------------
        // Drive USB_20_PORT_RESET via svt_usb_link_service on the host
        // agent's link_service_sequencer, accessed deterministically
        // through p_sequencer (svt_usb_virtual_sequencer).
        `uvm_info("USB_INIT",
            $sformatf("Issuing USB_20_PORT_RESET on %s",
                      p_sequencer.link_service_sequencer.get_full_name()),
            UVM_LOW)
        rst_seq = caliptra_ss_usb_port_reset_sequence::type_id::create("rst_seq");
        rst_seq.start(p_sequencer.link_service_sequencer);

        `uvm_info("USB_INIT",
            "Waiting ~100us for firmware to handle bus reset (DRES_C handler)...",
            UVM_LOW)
        #100us;

        // ---------------- GET_DESCRIPTOR(Device, addr=0) ----------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::DEVICE),
            .brequest              (8'h06),       // GET_DESCRIPTOR
            .wvalue                (16'h0100),    // DEVICE descriptor, index 0
            .windex                (16'h0000),
            .wlength               (16'h0012),    // 18 bytes
            .device_addr           (0),
            .label                 ("GET_DESC_DEV_addr0")
        );

        // ---------------- SET_ADDRESS(1) at addr=0 ----------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::HOST_TO_DEVICE),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::DEVICE),
            .brequest              (8'h05),       // SET_ADDRESS
            .wvalue                (16'h0001),    // new address = 1
            .windex                (16'h0000),
            .wlength               (16'h0000),
            .device_addr           (0),
            .label                 ("SET_ADDRESS_1")
        );

        // ---------------- GET_DESCRIPTOR(Device, addr=1) ----------------
        do_control_xfer(
            .bm_request_type_dir   (svt_usb_types::DEVICE_TO_HOST),
            .bm_request_type_type  (svt_usb_types::STANDARD),
            .bm_request_type_recip (svt_usb_types::DEVICE),
            .brequest              (8'h06),
            .wvalue                (16'h0100),
            .windex                (16'h0000),
            .wlength               (16'h0012),
            .device_addr           (1),
            .label                 ("GET_DESC_DEV_addr1")
        );

        `uvm_info("USB_INIT", "USB init sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_INIT_SEQUENCE_SV
