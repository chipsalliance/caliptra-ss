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

`ifndef CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV

// =============================================================================
// USB High-Speed device disconnect/reconnect sequence.
// Sequence flow:
//   1. Wait for HS host link ENABLED (initial connection).
//   2. Start SOF generation.
//   3. Hold 2 SOF intervals (~2 ms real time / scaledown factor).
//   4. Issue VIP protocol service to power off port (disconnect).
//   5. Wait for link state to leave ENABLED.
//   6. Wait ~6 ms real time.
//   7. Issue VIP protocol service to power on port (reconnect).
//   8. Wait for link to return to ENABLED (HS re-established).
//   9. Report success.
// =============================================================================
class caliptra_ss_usb_hs_dev_disconnect_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_disconnect_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_disconnect_sequence");
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
        svt_usb_agent        host_agent_h;
        uvm_component        parent_comp;
        svt_usb_status       shared_status;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_HS_DISC_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_HS_DISC_SEQ", "get_shared_status returned null.")

        // Step 1: Wait for initial HS link ENABLED.
        `uvm_info("USB_HS_DISC_SEQ", "Waiting for initial HS link ENABLED...", UVM_LOW)
        fork
            begin: WAIT_INIT
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_INIT;
            end
            begin: REPORT_INIT
                forever begin
                    #10us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("link_state=%p", shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DISC_SEQ", "HS link ENABLED (initial connection).", UVM_LOW)

        // Step 2: Start SOF generation.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
        end

        // Step 3: Hold 2 SOF intervals.
        #2us;

        // Step 4: Disconnect - power off port via VBUS off service.
        `uvm_info("USB_HS_DISC_SEQ", "Disconnecting (VBUS off)...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_vbus_off_sequence vbus_off;
            vbus_off = svt_usb_protocol_service_20_vbus_off_sequence::type_id::create("vbus_off");
            vbus_off.start(p_sequencer.prot_service_sequencer);
        end

        // Step 5: Wait for link to leave ENABLED.
        fork
            begin: WAIT_DISC
                wait (shared_status.link_usb_20_state != svt_usb_types::ENABLED);
                disable REPORT_DISC;
            end
            begin: REPORT_DISC
                forever begin
                    #5us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("Waiting disconnect: link=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_HS_DISC_SEQ", "Link left ENABLED state (disconnected).", UVM_LOW)

        // Step 6: Simulate 6 ms port power-off time.
        #6us;

        // Step 7: Reconnect - power on port via VBUS on service.
        `uvm_info("USB_HS_DISC_SEQ", "Reconnecting (VBUS on)...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_vbus_on_sequence vbus_on;
            vbus_on = svt_usb_protocol_service_20_vbus_on_sequence::type_id::create("vbus_on");
            vbus_on.start(p_sequencer.prot_service_sequencer);
        end

        // Step 8: Wait for HS link to re-establish.
        fork
            begin: WAIT_RECONN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_RECONN;
            end
            begin: REPORT_RECONN
                forever begin
                    #10us `uvm_info("USB_HS_DISC_SEQ",
                        $sformatf("Waiting reconnect: link=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join

        // Step 9: Report success.
        `uvm_info("USB_HS_DISC_SEQ",
            "HS disconnect/reconnect sequence complete - link re-established.", UVM_LOW)
        #10us;
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_DISCONNECT_SEQUENCE_SV
