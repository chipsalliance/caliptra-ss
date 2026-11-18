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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_ISO_TOKEN_MISMATCH_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_ISO_TOKEN_MISMATCH_TEST_SV

// =============================================================================
// caliptra_ss_usb_hs_dev_err_iso_token_mismatch: directed token/direction
// mismatch while an isochronous transaction is pending on EP2, HS, USBDC0.
//
// Stimulus for usb_transfer_outcome_cg.cp_errortype bin packet_unexpected
// (0x3) - the same bin caliptra_ss_usb_hs_dev_err_pkt_unexpected and
// caliptra_ss_usb_hs_dev_err_iso_stalled already close. This test's value is
// RTL line/branch coverage of usb_pie.m.vhdl lines 2192/2211/2231/2251, not
// new bin coverage. See the sequence header for the full rationale.
//
// ENDPOINT CONFIGURATION copied from caliptra_ss_usb_hs_dev_err_pkt_unexpected_test
// (same EP2 ISO IN/OUT slot layout) - see that file for the per-field notes.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_token_mismatch_test
//   +usb_errortype_check=1
//   +usb_errortype_check_sel=1
//   +usb_expect_errortype=3
// =============================================================================
class caliptra_ss_usb_hs_dev_err_iso_token_mismatch_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_err_iso_token_mismatch_test)

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_token_mismatch_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable at its default so the VIP chirps.
        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        // Extend to 3 endpoint_cfg slots and allocate the third.
        cfg.dev_cfg.local_device_cfg[0].num_endpoints   = 3;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();

        // slot [1]: EP2 ISO IN. Needed so the sequence's directed IN token
        // (used both to test line 2192 and to arm iso_in_pending_r ahead of
        // the line 2211 OUT-mismatch probe) targets a configured endpoint.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = 512;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;

        // slot [2]: EP2 ISO OUT - the endpoint the sequence's ISO OUT data
        // phases (which arm iso_out_pending_r) target.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = 2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size = 1024;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::HS;

        cfg.dev_cfg.local_device_cfg[0].device_timeout = 5000us;

        // The sequence takes no selector, so it is installed by type.
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_err_iso_token_mismatch_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // tend_to_end_delay_check is EXPECTED in this test.
    //
    // None of the four directed tokens the sequence sends (lines 2192/2211/
    // 2231/2251) is ever answered: each target branch returns the FSM to
    // WF_IDLE without reaching a DMA/ACK step, and isochronous transfers
    // never carry a handshake at all (USB 2.0 section 8.5.5). The VIP link
    // layer does not know the packet was deliberately unanswered, so it
    // starts its End-to-end Signal Delay timer and fails when nothing
    // answers. Same suppression API and precedent as
    // caliptra_ss_usb_hs_dev_err_iso_pid_seq_test and
    // caliptra_ss_usb_hs_dev_err_toggle_test, which document the full
    // rationale and the SVT API constraints (chk_cov_mgr.find() +
    // set_default_fail_effect(), run in end_of_elaboration_phase).
    // -------------------------------------------------------------------------
    svt_err_check_stats no_handshake_chk;

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);

        no_handshake_chk =
            env.host_agent.link.chk_cov_mgr.find("tend_to_end_delay_check");
        if (no_handshake_chk == null)
            `uvm_fatal("end_of_elaboration_phase",
                "chk_cov_mgr.find(\"tend_to_end_delay_check\") returned null")
        no_handshake_chk.set_default_fail_effect(svt_err_check_stats::EXPECTED);

        `uvm_info("end_of_elaboration_phase",
            "tend_to_end_delay_check set to EXPECTED: none of the four directed mismatch tokens is ever answered (isochronous transfers never carry a handshake), so the VIP's end-to-end delay timer on them is an expected artifact, not a sign the DUT or injection is broken.",
            UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_ISO_TOKEN_MISMATCH_TEST_SV

// File contains AI-generated response based on internal company sources
