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

`ifndef CALIPTRA_SS_USB_FS_CLOCK_SEQUENCE_SV
`define CALIPTRA_SS_USB_FS_CLOCK_SEQUENCE_SV

// =============================================================================
// USB Full-Speed clock sequence.
// Companion sequence for the caliptra_ss_usb_fs_clock test. Unlike the init
// sequence (caliptra_ss_usb_init_sequence) which drives enumeration control
// transfers, this sequence only:
//   1. Waits for the host link to reach ENABLED state (link-up / FS attach).
//   2. Starts SOF generation to keep the link alive.
//   3. Holds the objection for a configurable observation window so the TB
//      clock frequency checker bound to clk_src_usb_o has time to measure
//      and report.
// No protocol transfers are issued. The DUT USB clock path is exercised purely
// by the MCU firmware (boot_usb_core + idle loop) and the VIP link state
// machine; this sequence only synchronises the UVM timeline with the hardware.
// Usage:
//   Set as default_sequence on env.host_agent.virt_sequencer.main_phase via
//   uvm_config_db (see caliptra_ss_usb_fs_clock_test).
// =============================================================================
class caliptra_ss_usb_fs_clock_sequence extends uvm_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_clock_sequence)
    `uvm_declare_p_sequencer(svt_usb_virtual_sequencer)

    // Observation window: how long (in us) to hold the UVM main_phase objection
    // after the link reaches ENABLED so the TB clock checker can complete its
    // NUM_EDGES measurement.  Default 100 us covers 100 edges at 48 MHz easily.
    int unsigned obs_window_us = 100;

    function new(string name = "caliptra_ss_usb_fs_clock_sequence");
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

        // Resolve parent agent handle.
        parent_comp = p_sequencer.get_parent();
        if (!$cast(host_agent_h, parent_comp)) begin
            `uvm_fatal("USB_FS_CLK_SEQ",
                $sformatf("Cannot cast p_sequencer parent (%s) to svt_usb_agent",
                          parent_comp.get_full_name()))
        end

        shared_status = p_sequencer.get_shared_status(this);
        if (shared_status == null)
            `uvm_fatal("USB_FS_CLK_SEQ",
                "p_sequencer.get_shared_status(this) returned null.")

        `uvm_info("USB_FS_CLK_SEQ",
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
                    #10us `uvm_info("USB_FS_CLK_SEQ",
                        $sformatf("host agent link_usb_20_state [%p]",
                                  shared_status.link_usb_20_state),
                        UVM_LOW);
                end
            end
        join

        `uvm_info("USB_FS_CLK_SEQ",
            "Host link ENABLED. Starting SOF generation.", UVM_LOW)

        // Start SOF generation so the FS link stays active during the
        // observation window. Without SOF the VIP link FSM will transition
        // to SUSPENDED within the idle timeout.
        begin
            svt_usb_protocol_service_20_sof_on_sequence sof_on_seq;
            sof_on_seq = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on_seq");
            sof_on_seq.start(p_sequencer.prot_service_sequencer);
            `uvm_info("USB_FS_CLK_SEQ", "SOF generation started.", UVM_LOW)
        end

        // Hold the objection for the observation window. The TB clock checker
        // (caliptra_ss_usb_fs_clock_checker.sv) measures clk_src_usb_o during
        // this window and issues $display/$error with the result.
        `uvm_info("USB_FS_CLK_SEQ",
            $sformatf("Holding observation window for %0d us.", obs_window_us),
            UVM_LOW)
        #(obs_window_us * 1us);

        `uvm_info("USB_FS_CLK_SEQ",
            "USB FS clock observation window complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_FS_CLOCK_SEQUENCE_SV
