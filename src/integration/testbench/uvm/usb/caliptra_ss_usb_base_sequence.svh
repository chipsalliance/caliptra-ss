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

`ifndef CALIPTRA_SS_USB_BASE_SEQUENCE_SV
`define CALIPTRA_SS_USB_BASE_SEQUENCE_SV

// =============================================================================
// caliptra_ss_usb_base_sequence
//
// Common base for USB host-side sequences that talk to the DUT through the
// VIP svt_usb_virtual_sequencer (xfer_sequencer + link/protocol service
// sequencers). Provides:
//   * Objection plumbing for stand-alone start() from a phase.
//   * resolve_xfer_handles() - canonical accessor for host_agent,
//     svt_usb_configuration, and svt_usb_status off the virtual sequencer.
//   * do_control_xfer() - VIP-canonical single CONTROL transfer issuance
//     (USB 2.0 sec 9.3, 9.4). Uses set cfg + fix_anchors + randomize-with
//     pattern (see VIP example usb_directed_transfers_sequence.sv).
//   * wait_xfer_done() - blocks on the agent prot
//     NOTIFY_USB_TRANSFER_ENDED trigger (VIP example
//     attach_bulk_xfers_detach_hs_sequence.sv).
//
// Sequences that need to share this scaffolding (init sequence, OCP
// recovery class-transfer sequence, etc.) MUST extend this class so the
// CONTROL-xfer choreography stays in one place and message tags ("USB_INIT")
// remain consistent for log scraping.
// =============================================================================
class caliptra_ss_usb_base_sequence extends uvm_sequence #(svt_usb_transfer);

    `uvm_object_utils(caliptra_ss_usb_base_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_base_sequence");
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

    virtual task resolve_xfer_handles(
        output svt_usb_agent host_agent_h,
        output svt_usb_configuration usb_cfg,
        output svt_usb_status shared_status);

        uvm_component parent_comp;
        svt_configuration get_cfg;

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
            `uvm_fatal("USB_INIT",
                "Unable to cast configuration to svt_usb_configuration")
    endtask

    task do_control_xfer(
        input bit [7:0] bm_request_type_dir,
        input bit [7:0] bm_request_type_type,
        input bit [7:0] bm_request_type_recip,
        input bit [7:0] brequest_val,
        input bit [15:0] wvalue,
        input bit [15:0] windex,
        input bit [15:0] wlength,
        input int device_addr,
        input string label,
        input svt_usb_configuration usb_cfg = null);

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
            `uvm_fatal("USB_INIT",
                $sformatf("svt_usb_transfer randomize() failed for %s", label))
        end
        finish_item(req, -1);
        `uvm_info("USB_INIT",
            $sformatf("CONTROL %s done (addr=%0d wValue=0x%04x wLength=0x%04x)",
                      label, device_addr, wvalue, wlength), UVM_NONE)
    endtask

    task wait_xfer_done(svt_usb_agent agent_h, string label);
        agent_h.prot.NOTIFY_USB_TRANSFER_ENDED.wait_trigger();
        `uvm_info("USB_INIT",
            $sformatf("Transfer %s completed on bus.", label), UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_BASE_SEQUENCE_SV
