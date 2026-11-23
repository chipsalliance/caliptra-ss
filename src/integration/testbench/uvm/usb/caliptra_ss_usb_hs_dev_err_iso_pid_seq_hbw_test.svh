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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_HBW_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_HBW_TEST_SV

// =============================================================================
// caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw: out-of-sequence DATA0 PID on a
// high-bandwidth isochronous OUT endpoint, HS, USBDC0.
//
// Forked from caliptra_ss_usb_hs_dev_err_iso_pid_seq_test (same EP2 ISO
// IN/OUT slot layout) solely to target usb_pie.m.vhdl line 2704, which
// requires the OPPOSITE endpoint configuration (high-bandwidth) from that
// suite's deliberately non-HBW setup - see the sequence header for the full
// rationale on why this is a fork, not an edit.
//
// Stimulus for usb_transfer_outcome_cg.cp_errortype bin pid_unknown (0x2),
// driven from usb_pie.m.vhdl line 2704. See the sequence header for why a
// prior legitimate MDATA phase is required before the mismatching DATA0.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_test
//   +usb_errortype_check=1
//   +usb_errortype_check_sel=1
//   +usb_expect_errortype=2
// =============================================================================
class caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_test)

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_test",
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

        // slot [1]: EP2 ISO IN. Not driven by this test, but the slot layout
        // must match the one the anchor indices assume.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = 512;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;

        // slot [2]: EP2 ISO OUT - the endpoint this test drives the directed
        // OUT token + MDATA/DATA0 packets against. max_packet_size is left at
        // the VIP-model packet size (1024, matching the data phases' payload
        // size); the HIGH-BANDWIDTH NBYTES encoding that matters for line
        // 2704 is a firmware/RTL-side descriptor field
        // (caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw.c's USB_EP2_OUT_NBYTES),
        // not a VIP endpoint_cfg field.
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
            caliptra_ss_usb_hs_dev_err_iso_pid_seq_hbw_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // tend_to_end_delay_check is EXPECTED in this test.
    //
    // The sequence's second data phase (mismatching DATA0) is never
    // answered: usb_pie.m.vhdl's PID_DATA0-unexpected branch (line 2704)
    // reports pid_unknown and returns the FSM to WF_IDLE without ever
    // reaching a DMA/ACK step, and isochronous transfers carry no handshake
    // at all (USB 2.0 section 8.5.5). Same suppression API and precedent as
    // caliptra_ss_usb_hs_dev_err_iso_pid_seq_test, which documents the full
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
            "tend_to_end_delay_check set to EXPECTED: the mismatching DATA0 packet is unexpected on this endpoint, and isochronous transfers never carry a handshake, so the VIP's end-to-end delay timer on it is an expected artifact, not a sign the DUT or injection is broken.",
            UVM_LOW)
    endfunction

endclass


`endif // CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_HBW_TEST_SV

// File contains AI-generated response based on internal company sources
