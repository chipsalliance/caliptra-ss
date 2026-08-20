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

`ifndef CALIPTRA_SS_USB_USBD_CONN_SEQUENCE_SV
`define CALIPTRA_SS_USB_USBD_CONN_SEQUENCE_SV

// =============================================================================
// USB device (USBD) basic connection sequence.

// Sequence flow:
//   1. Wait for FS host link to reach ENABLED (device D+ pullup detected,
//      reset/chirp completed, link in FS ENABLED state).
//   2. Start SOF generation to keep the FS link alive.
//   3. Hold an observation window for MCU firmware to confirm connection
//      and log the result.
// =============================================================================

class caliptra_ss_usb_usbd_conn_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_usbd_conn_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    int unsigned obs_window_us = 100;

    function new(string name = "caliptra_ss_usb_usbd_conn_sequence");
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

    virtual task body();
        svt_usb_agent  host_agent_h;
        uvm_component  parent_comp;
        svt_usb_status shared_status;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_USBD_CONN_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_USBD_CONN_SEQ", "get_shared_status returned null.")

        // Step 1: Wait for FS link ENABLED.
        `uvm_info("USB_USBD_CONN_SEQ",
            $sformatf("Waiting for FS host link ENABLED (current=%p)...",
                      shared_status.link_usb_20_state), UVM_LOW)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK;
            end
            begin: REPORT_LINK
                forever begin
                    #10us `uvm_info("USB_USBD_CONN_SEQ",
                        $sformatf("link_usb_20_state=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_USBD_CONN_SEQ", "FS host link ENABLED - device connection confirmed.", UVM_LOW)

        // Step 2: Start SOF generation to keep the FS link alive.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
                "sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_USBD_CONN_SEQ", "SOF generation started.", UVM_LOW)
        end

        // Step 3: Observation window for MCU firmware to log connection result.
        `uvm_info("USB_USBD_CONN_SEQ",
            $sformatf("Holding observation window for %0d us.", obs_window_us), UVM_LOW)
        #(obs_window_us * 1us);

        `uvm_info("USB_USBD_CONN_SEQ",
            "USB device basic connection sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_USBD_CONN_SEQUENCE_SV
