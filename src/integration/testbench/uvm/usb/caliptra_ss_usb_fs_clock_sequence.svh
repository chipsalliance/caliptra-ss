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
//   1. Waits for the host link to reach ENABLED state (link-up / FS attach),
//      bounded by a timeout that raises a uvm_error rather than hanging.
//   2. Starts SOF generation to keep the link alive.
//   3. Holds the objection for a configurable observation window so the TB
//      link-speed checker (caliptra_ss_usb_fs_speed_checker.sv, observing the
//      UTMI interface) has time to measure and report.
// No protocol transfers are issued. The DUT USB path is exercised purely by
// the MCU firmware (boot_usb_core_fs + hub connect + idle loop) and the VIP
// link state machine; this sequence only synchronises the UVM timeline with
// the hardware.
// Usage:
//   Set as default_sequence on env.host_agent.virt_sequencer.main_phase via
//   uvm_config_db (see caliptra_ss_usb_fs_clock_test).
// =============================================================================
// Extends caliptra_ss_usb_base_sequence (see caliptra_ss_usb_base_sequence.svh)
// for pre_start()/post_start(), the handle resolvers, the bounded
// wait_for_link_enabled() link wait and start_sof_generation(). This sequence
// issues no control or data transfers of its own.
class caliptra_ss_usb_fs_clock_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_fs_clock_sequence)

    // Observation window held open after SOF generation starts, so the TB
    // speed checker has live FS traffic to measure.
    //
    // This must close BEFORE the MCU firmware halts, otherwise the
    // observation-window-done event below is never triggered and the checker's
    // completeness guard never runs, which would let unevaluated checks pass
    // silently. Measured timeline: first packet arrives about 308 us and the
    // MCU halts about 405 us, so 60 us closes the window near 368 us and
    // leaves roughly 35 us of margin.
    int unsigned obs_window_us = 60;

    // Name of the global uvm_event triggered when the observation window
    // closes. Must match OBS_WINDOW_EVENT in
    // caliptra_ss_usb_fs_speed_checker.sv.
    string obs_window_event_name = "usb_fs_obs_window_done";

    // Upper bound (in us) on how long to wait for the host link to reach
    // ENABLED. Without a bound, a device or hub that never connects leaves
    // this sequence waiting forever and the run dies on the far coarser
    // MCU-halt timeout with no indication of the real cause.
    int unsigned link_up_timeout_us = 3000;

    function new(string name = "caliptra_ss_usb_fs_clock_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_status shared_status;

        // Resolves via the base class instead of re-implementing the
        // cast/null-check inline (see caliptra_ss_usb_base_sequence.svh).
        shared_status = resolve_shared_status();

        // Bounded link wait from the base class. On timeout it raises the
        // uvm_error and sets link_wait_timed_out, so the observation window
        // below is skipped rather than measuring a dead link.
        wait_for_link_enabled(shared_status, "FS host link", link_up_timeout_us);
        if (link_wait_timed_out)
            return;

        // Start SOF generation so the FS link stays active during the
        // observation window. Without SOF the VIP link FSM will transition
        // to SUSPENDED within the idle timeout. Uses the base class helper
        // (see caliptra_ss_usb_base_sequence.svh) instead of re-implementing
        // the sof_on_seq create/start inline.
        start_sof_generation();

        // Hold the objection for the observation window. The TB speed checker
        // (caliptra_ss_usb_fs_speed_checker.sv) samples the UTMI interface
        // during this window and reports via uvm_report_info/uvm_report_error.
        `uvm_info("USB_FS_CLK_SEQ",
            $sformatf("Holding observation window for %0d us.", obs_window_us),
            UVM_LOW)
        #(obs_window_us * 1us);

        `uvm_info("USB_FS_CLK_SEQ",
            "USB FS clock observation window complete.", UVM_LOW)

        // Release the TB speed checker's completeness guard. This is done
        // unconditionally on every path that reaches the end of the window, so
        // the checker always gets the chance to report unevaluated checks while
        // the run phase is still active and uvm_report_error still counts
        // toward the final verdict.
        begin
            uvm_event obs_window_done;
            obs_window_done = uvm_event_pool::get_global(obs_window_event_name);
            obs_window_done.trigger();
            `uvm_info("USB_FS_CLK_SEQ",
                $sformatf("Triggered %s for the TB speed checker.",
                          obs_window_event_name),
                UVM_LOW)
        end
    endtask

endclass

`endif // CALIPTRA_SS_USB_FS_CLOCK_SEQUENCE_SV
