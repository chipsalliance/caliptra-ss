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

`ifndef CALIPTRA_SS_USB_HS_DEV_REMOTE_WAKEUP_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_REMOTE_WAKEUP_SEQUENCE_SV

// =============================================================================
// USB HS device remote wakeup sequence.
//
// Sequence flow:
//   1. Wait for HS host link to reach ENABLED.
//   2. Start SOF generation to keep the HS link alive.
//   3. Settling delay to allow VIP link SM to stabilize in ENABLED before SUSPEND.
//   4. Host drives SUSPEND signaling (SOF_OFF).
//   5. Wait for VIP link SM to reach SUSPENDED state.
//   6. Suspend dwell: allow MCU firmware time to detect DSUS_C (suspend entry).
//   7. Host drives resume K-state via svt_usb_link_service_clear_suspend_sequence
//      on link_service_sequencer. This is the only VIP sequence that actually
//      drives K-state on the bus; resume_transfer_processing_sequence must NOT
//      be used here because it drives zero bus activity and returns instantly.
//   8. Restart SOF generation to hold link ENABLED after resume.
//   9. Poll for link ENABLED after resume.
//  10. Observation window for MCU firmware to log DSUS_C resume event.
// =============================================================================

class caliptra_ss_usb_hs_dev_remote_wakeup_sequence extends uvm_sequence;
    `uvm_object_utils(caliptra_ss_usb_hs_dev_remote_wakeup_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_hs_dev_remote_wakeup_sequence");
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
        svt_usb_agent    host_agent_h;
        uvm_component    parent_comp;
        svt_usb_status   shared_status;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("CALIPTRA_SS_USB_HS_D",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("CALIPTRA_SS_USB_HS_D", "get_shared_status returned null.")

        // Step 1: Wait for HS link ENABLED.
        fork
            begin: WE
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable RE;
            end
            begin: RE
                forever begin
                    #10us `uvm_info("CALIPTRA_SS_USB_HS_D",
                        $sformatf("link=%p", shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("CALIPTRA_SS_USB_HS_D", "HS link ENABLED.", UVM_LOW)

        // Step 2: Start SOF generation.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on;
            sof_on = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on");
            sof_on.start(p_sequencer.prot_service_sequencer);
            `uvm_info("CALIPTRA_SS_USB_HS_D", "SOF generation started.", UVM_LOW)
        end

        // Step 3: Settling delay after link-up.
        // The VIP link SM transitions through TRANSMIT -> ENABLED in the first
        // few microseconds after bus reset. Issuing SOF_OFF inside that window
        // causes the link to go DISCONNECTED and trigger an unintended second
        // bus-reset cycle. 500us ensures the link is fully stable with SOF
        // running before suspend is driven.
        #500us;

        // Step 4: Host drives SUSPEND signaling.
        `uvm_info("USB_HS_DEV_RW_SEQ", "Suspending link...", UVM_LOW)
        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end
        `uvm_info("USB_HS_DEV_RW_SEQ", "SUSPEND signaling complete.", UVM_LOW)

        // Step 5: Wait for VIP link SM to reach SUSPENDED state.
        // SOF_OFF returns immediately; the 3ms USB 2.0 idle timer runs inside
        // the VIP. We must confirm SUSPENDED before proceeding so that the
        // MCU has a real suspended-bus condition to observe.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::SUSPENDED
                   && poll_cnt < 10000) begin
                #1us; poll_cnt++;
            end
            if (shared_status.link_usb_20_state == svt_usb_types::SUSPENDED)
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    $sformatf("VIP link SUSPENDED after %0d us.", poll_cnt), UVM_LOW)
            else
                `uvm_error("USB_HS_DEV_RW_SEQ", "Timeout waiting for VIP link SUSPENDED.")
        end

        // Step 6: Suspend dwell - give MCU firmware time to detect DSUS_C.
        // From the log, SUSPENDED state arrives ~180 us after SOF_OFF but the
        // MCU polling loop does not sample DEVCMDSTAT until ~614 us after that.
        // 2ms is a safe margin for the firmware to see and print "Suspend change
        // event 1" before the host drives resume signaling.
        #2ms;

        // Step 7: Host drives resume K-state on the bus.
        // svt_usb_link_service_clear_suspend_sequence is the correct sequence:
        // it drives K-state from the host side and transitions the link SM
        // SUSPENDED -> S_RESUME -> ENABLED.
        // svt_usb_protocol_service_resume_transfer_processing_sequence must NOT
        // be used here: it drives no bus activity and returns at zero sim-time.
        `uvm_info("USB_HS_DEV_RW_SEQ", "Host driving resume K-state (clear_suspend)...", UVM_LOW)
        begin
            svt_usb_link_service_clear_suspend_sequence clr_susp;
            clr_susp = svt_usb_link_service_clear_suspend_sequence::type_id::create("clr_susp");
            clr_susp.start(p_sequencer.link_service_sequencer);
        end
        `uvm_info("USB_HS_DEV_RW_SEQ", "Host resume K-state complete.", UVM_LOW)

        // Step 8: Restart SOF generation after resume.
        // Without SOF the VIP link SM re-enters SUSPEND after the keepalive
        // timeout (~3ms). SOF must be restarted immediately after clear_suspend.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on2;
            sof_on2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on2");
            sof_on2.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_DEV_RW_SEQ", "SOF restarted after resume.", UVM_LOW)
        end

        // Step 9: Poll for link ENABLED after resume.
        // Allow up to 50ms (50000 x 1us) for the link to re-ENABLE.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::ENABLED && poll_cnt < 50000) begin
                #1us; poll_cnt++;
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    $sformatf("Waiting ENABLED: link=%0s cnt=%0d",
                        shared_status.link_usb_20_state.name(), poll_cnt), UVM_HIGH)
            end
            if (shared_status.link_usb_20_state == svt_usb_types::ENABLED)
                `uvm_info("USB_HS_DEV_RW_SEQ",
                    "Remote wakeup complete - link ENABLED.", UVM_LOW)
            else
                `uvm_error("USB_HS_DEV_RW_SEQ",
                    $sformatf("Timeout waiting for ENABLED; link=%0s",
                        shared_status.link_usb_20_state.name()))
        end

        // Step 10: Observation window for MCU firmware to log DSUS_C resume event.
        // 200us gives the MCU polling loop enough iterations to sample DEVCMDSTAT
        // and print "Suspend change event 2" before the sequence ends.
        #200us;

        `uvm_info("CALIPTRA_SS_USB_HS_D",
            "caliptra_ss_usb_hs_dev_remote_wakeup_sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_REMOTE_WAKEUP_SEQUENCE_SV
