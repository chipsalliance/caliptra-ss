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

`ifndef CALIPTRA_SS_USB_DEV_REG_RW_TEST_SV
`define CALIPTRA_SS_USB_DEV_REG_RW_TEST_SV

// =============================================================================
// USB device-controller register RW test.
//
// Standalone register read/write access test for BOTH embedded USB device
// controllers (USBDC0 / dev0 and USBDC1 / dev1) in a single run. All register
// checking is performed by the MCU firmware (caliptra_ss_usb_dev_reg_rw.c),
// which walks a shared register-disposition table over both banks directly
// over the MCU LSU AXI master:
//   - RW registers: masked random write / read-back compare.
//   - RO registers: three distinct writes, proving the RO bits are immutable.
//
// This test does NOT bring up the USB link and drives no USB traffic. Unlike
// caliptra_ss_usb_fs_clock_test it therefore leaves the base-test host cfg
// untouched (no high_speed_capable override) and simply installs
// caliptra_ss_usb_mem_rw_sequence as the main_phase default sequence. That
// sequence just holds the phase objection open long enough for the firmware to
// finish and report its verdict.
//
// Verdict (two judges):
//   - firmware DEBUG_OUT byte (TB_CMD_TEST_PASS / TB_CMD_TEST_FAIL), and
//   - UVM error count checked in caliptra_ss_usb_base_test::final_phase.
//
// NOTE: the VIP link check tdcnn_check is deliberately marked EXPECTED by
// end_of_elaboration_phase below, so it cannot contribute to the UVM error
// count judge. See the comment on that function for the rationale. Every
// other VIP check remains active.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_dev_reg_rw_test
// =============================================================================
class caliptra_ss_usb_dev_reg_rw_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_dev_reg_rw_test)

    // Handle for the suppressed VIP connect-signalling check. Held as a class
    // member so the object outlives end_of_elaboration_phase.
    svt_err_check_stats no_link_chk;

    function new(string name = "caliptra_ss_usb_dev_reg_rw_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        caliptra_ss_usb_mem_rw_sequence mem_rw_seq;

        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // Install the shared standalone access sequence as the default on the
        // host virtual sequencer so it runs automatically during main_phase.
        // No host cfg override: the link is intentionally left un-brought-up.
        // The register walk is short (a handful of AXI reads/writes per
        // register over two banks), so the dominant cost is MCU boot; 1500 us
        // gives generous margin before the coarse MCU-halt timeout closes the
        // run. The sequence OBJECT is registered rather than its type wrapper
        // so this per-test window can be set as a field.
        mem_rw_seq = caliptra_ss_usb_mem_rw_sequence::type_id::create("mem_rw_seq");
        mem_rw_seq.run_window_us = 1500;
        mem_rw_seq.window_desc   = "both device register bank checks";

        uvm_config_db#(uvm_sequence_base)::set(this,
            "env.host_agent.virt_sequencer.main_phase",
            "default_sequence",
            mem_rw_seq);

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // end_of_elaboration_phase: suppress the tdcnn_check false positive.
    //
    // This test never brings the USB link up (no attach, no bus traffic), so
    // DP/DM are left undriven. The VIP connect-detect FSM still sees a
    // transient LINESTATE_J -> LINESTATE_SE0 edge (observed at ~96 us) and
    // fires:
    //   [register_fail:LINK 20 TIMING CHECKS:HOST:tdcnn_check]
    //   cfg.tdcnn_min=250 ns (spec=2500 ns) start_end_time_delta=143.754 ns
    //
    // tdcnn is a connect-signalling timing check (USB2.0 spec 7.1.7.3). With
    // no real attach taking place there is nothing legitimate for it to
    // measure, so this is a pure false positive.
    //
    // Raising cfg.tdcnn_min is NOT a usable fix: the value is already scaled
    // down to 250 ns from the 2500 ns spec by the USB_VIP_SCALEDOWN_TIMER
    // preset, and the observed glitch is 143 ns. Any threshold low enough to
    // pass would be meaningless, and raising it changes connect-detect
    // behaviour for the wrong reason. Suppression is the correct lever.
    //
    // SVT checks are NOT suppressible via
    // uvm_root.set_report_severity_id_override() because SVT fires them
    // through its own svt_err_check_stats infrastructure, bypassing the UVM
    // report handler. The supported SVT API is:
    //   chk = agent.link.chk_cov_mgr.find("short_check_name");
    //   chk.set_default_fail_effect(svt_err_check_stats::EXPECTED);
    // This must run in end_of_elaboration_phase, when the agent hierarchy is
    // fully constructed and chk_cov_mgr is populated.
    //
    // Scope: this override is local to this test class only; no other USB
    // test loses tdcnn_check coverage. If this test is ever extended to
    // actually bring the link up, remove this suppression first, otherwise a
    // real connect-timing failure would be masked.
    // -------------------------------------------------------------------------
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);

        no_link_chk = env.host_agent.link.chk_cov_mgr.find("tdcnn_check");
        if (no_link_chk == null)
            `uvm_fatal("end_of_elaboration_phase",
                "chk_cov_mgr.find(\"tdcnn_check\") returned null")
        no_link_chk.set_default_fail_effect(svt_err_check_stats::EXPECTED);

        `uvm_info("end_of_elaboration_phase",
            "tdcnn_check set to EXPECTED (link is intentionally never brought up).",
            UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DEV_REG_RW_TEST_SV
