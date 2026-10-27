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

`ifndef CALIPTRA_SS_USB_HS_DEV_RESUME_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_RESUME_SEQUENCE_SV

class caliptra_ss_usb_hs_dev_resume_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_resume_sequence)

    function new(string name = "caliptra_ss_usb_hs_dev_resume_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] body() begin - hub-composite HS resume sequence starting.", UVM_NONE)

        // Start SOF so the link can negotiate HS and reach ENABLED.
        start_sof_generation();

        `uvm_info("USB_HS_RES_SEQ", "[DBG] Phase: waiting for HS link ENABLED.", UVM_NONE)
        wait_for_link_enabled(shared_status, "HS host link");

        // Allow MCU firmware to finish initial EP0 arming before the first SETUP
        // packet arrives. 20 us matches the settling delay used in hs_dev_nbyte.
        #20us;

        // Hub-aware enumeration (hub-composite IP). USBDC0 sits BEHIND an
        // on-chip 2-port hub, so the host enumerates the HUB at addr 1 (step A),
        // brings up its downstream port 1 (step B), then enumerates USBDC0 at
        // addr 2 (step C). No GET_CONFIGURATION read-back is issued here.
        // See claude_md/09_usb_hub_composite_migration.md section E.
        enumerate_hub_and_usbdc0(host_agent_h, usb_cfg, "", 0);

        `uvm_info("USB_HS_RES_SEQ","Enumeration done.",UVM_LOW)
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Hub-aware enumeration complete; USBDC0 addressed at 2.",
            UVM_NONE)
        #10us;



        // --- Suspend: stop SOF so device enters suspend state ---
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] Phase: SUSPEND - stopping SOF, holding 2500us.", UVM_NONE)
        `uvm_info("USB_HS_RES_SEQ","Suspending (SOF OFF)...",UVM_LOW)

        begin
            svt_usb_protocol_service_20_sof_off_sequence susp;
            susp = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("susp");
            susp.start(p_sequencer.prot_service_sequencer);
        end
        $display("SOF stopped");
        // Hold suspended for at least 2500 us. usb_timers_sf uses a Clk1kHz-based
        // suspend timer (SUSPEND_TIME=1 means DeviceSuspended asserts on the 2nd
        // Clk1kHz tick = 2 ms minimum at 48 MHz). 500 us was too short; DSUS never
        // asserted. 2500 us provides 2 ms for the timer plus 500 us margin.
        #2500us;

        // --- Resume: Force Port Resume (K-state) ---
        // Drive K on the bus via the link service sequencer. This sends the
        // USB_20_CLEAR_PORT_SUSPEND command which causes the VIP host to drive
        // K for the spec-required duration and then end-of-resume signaling.
        // Prerequisites: bus must be in SUSPENDED state.
        `uvm_info("USB_HS_RES_SEQ",
            $sformatf("[DBG] Phase: RESUME - driving FPR (K) to USBDC0 addr=%0d.",
                usb_cfg.remote_device_cfg[0].device_address), UVM_NONE)
        `uvm_info("USB_HS_RES_SEQ","Resuming (FPR) - driving K on bus...",UVM_LOW)
        begin
            svt_usb_link_service_clear_suspend_sequence link_resume_seq;
            link_resume_seq = svt_usb_link_service_clear_suspend_sequence::type_id::create("link_resume_seq");
            link_resume_seq.device_address = usb_cfg.remote_device_cfg[0].device_address;
            link_resume_seq.start(p_sequencer.link_service_sequencer);
        end

        $display("FPR resuming done");

        // Restart SOF after FPR. The link_service_clear_suspend sequence drives
        // K and end-of-resume but does NOT restart SOF; without it the VIP link
        // SM re-enters SUSPEND after the keepalive timeout.
        
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq2;
            sof_on_seq2 = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq2");
            sof_on_seq2.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_HS_RES_SEQ","SOF restarted after resume.",UVM_LOW)
        end

        // Wait for link to return to ENABLED after resume.
        begin
            int unsigned poll_cnt = 0;
            while (shared_status.link_usb_20_state != svt_usb_types::ENABLED && poll_cnt < 1000) begin
                #1us; poll_cnt++;
                `uvm_info("USB_HS_RES_SEQ",
                    $sformatf("Waiting ENABLED: link=%0s cnt=%0d",
                        shared_status.link_usb_20_state.name(), poll_cnt), UVM_HIGH)
            end
            if (shared_status.link_usb_20_state == svt_usb_types::ENABLED) begin
                `uvm_info("USB_HS_RES_SEQ",
                    $sformatf("[DBG] RESUME result: link ENABLED after %0d us poll.",
                        poll_cnt), UVM_NONE)
                `uvm_info("USB_HS_RES_SEQ","Device resumed - link ENABLED.",UVM_LOW)
            end
            else begin
                `uvm_info("USB_HS_RES_SEQ",
                    $sformatf("[DBG] RESUME result: TIMEOUT, link=%0s.",
                        shared_status.link_usb_20_state.name()), UVM_NONE)
                `uvm_error("USB_HS_RES_SEQ",
                    $sformatf("Timeout waiting for ENABLED after FPR; link=%0s",
                        shared_status.link_usb_20_state.name()))
            end
        end
        #100us;
        `uvm_info("USB_HS_RES_SEQ",
            "[DBG] body() end - sequence complete.", UVM_NONE)
        `uvm_info("USB_HS_RES_SEQ","caliptra_ss_usb_hs_dev_resume_sequence complete.",UVM_LOW)

    endtask
endclass

`endif // CALIPTRA_SS_USB_HS_DEV_RESUME_SEQUENCE_SV
