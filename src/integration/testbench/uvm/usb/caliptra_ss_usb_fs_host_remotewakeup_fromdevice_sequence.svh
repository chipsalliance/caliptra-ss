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

`ifndef CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV

// =============================================================================
// USB Full-Speed host remote wakeup from device sequence.

// Sequence flow:
//   1. Wait for FS host link to reach ENABLED.
//   2. Start SOF generation to keep the FS link alive.
//   3. Short delay for MCU firmware to stabilize.
//   4. Host drives SUSPEND signaling via SVT protocol service.
//   5. Delay to allow device firmware to assert K resume.
//   6. Host detects device K resume and drives RESUME signaling.
//   7. Wait for link to return to ENABLED after resume.
//   8. Observation window for MCU firmware to log result.
// =============================================================================

class caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    function new(string name = "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence");
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
        svt_usb_agent                                host_agent_h;
        uvm_component                                parent_comp;
        svt_usb_status                               shared_status;
        svt_usb_protocol_service_20_suspend_sequence suspend_seq;
        svt_usb_protocol_service_20_resume_sequence  resume_seq;

        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp))
            `uvm_fatal("USB_FS_REMWAKE_DEV_SEQ",
                $sformatf("Cannot cast parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_FS_REMWAKE_DEV_SEQ", "get_shared_status returned null.")

        // Step 1: Wait for FS link ENABLED.
        `uvm_info("USB_FS_REMWAKE_DEV_SEQ",
            $sformatf("Waiting for FS host link ENABLED (current=%p)...",
                      shared_status.link_usb_20_state), UVM_LOW)
        fork
            begin: WAIT_EN
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_LINK;
            end
            begin: REPORT_LINK
                forever begin
                    #10us `uvm_info("USB_FS_REMWAKE_DEV_SEQ",
                        $sformatf("link_usb_20_state=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_FS_REMWAKE_DEV_SEQ", "FS host link ENABLED.", UVM_LOW)

        // Step 2: Start SOF generation.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
                "sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_FS_REMWAKE_DEV_SEQ", "SOF generation started.", UVM_LOW)
        end

        // Step 3: Short delay for MCU firmware to stabilize after link-up.
        #2us;

        // Step 4: Host drives SUSPEND signaling. Device firmware will detect
        // SUSP interrupt and assert remote wakeup K resume after the suspend
        // interval expires.
        `uvm_info("USB_FS_REMWAKE_DEV_SEQ", "Host driving SUSPEND...", UVM_LOW)
        suspend_seq = svt_usb_protocol_service_20_suspend_sequence::type_id::create(
            "suspend_seq");
        suspend_seq.start(p_sequencer.prot_service_sequencer);
        `uvm_info("USB_FS_REMWAKE_DEV_SEQ", "SUSPEND signaling complete.", UVM_LOW)

        // Step 5: Delay to allow device firmware to assert K resume.

        #5us;

        // Step 6: Host detects device-driven K resume and responds with RESUME.
        `uvm_info("USB_FS_REMWAKE_DEV_SEQ",
            "Host driving RESUME in response to device remote wakeup...", UVM_LOW)
        resume_seq = svt_usb_protocol_service_20_resume_sequence::type_id::create(
            "resume_seq");
        resume_seq.start(p_sequencer.prot_service_sequencer);
        `uvm_info("USB_FS_REMWAKE_DEV_SEQ", "RESUME signaling complete.", UVM_LOW)

        // Step 7: Wait for link to return to ENABLED after resume.
        fork
            begin: WAIT_ENABLED_AFTER_RESUME
                wait (shared_status.link_usb_20_state == svt_usb_types::ENABLED);
                disable REPORT_RESUME_STATE;
            end
            begin: REPORT_RESUME_STATE
                forever begin
                    #10us `uvm_info("USB_FS_REMWAKE_DEV_SEQ",
                        $sformatf("post-resume link_usb_20_state=%p",
                                  shared_status.link_usb_20_state), UVM_LOW);
                end
            end
        join
        `uvm_info("USB_FS_REMWAKE_DEV_SEQ", "Link re-ENABLED after resume.", UVM_LOW)

        // Step 8: Observation window for MCU firmware to log result.
        #10us;

        `uvm_info("USB_FS_REMWAKE_DEV_SEQ",
            "USB FS host remote wakeup from device sequence complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_FS_HOST_REMOTEWAKEUP_FROMDEVICE_SEQUENCE_SV
