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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_TEST_SV

// =============================================================================
// caliptra_ss_usb_hs_dev_err_iso_pid_seq: out-of-sequence MDATA PID on a
// single-buffer isochronous OUT endpoint, HS, USBDC0.
//
// Stimulus for usb_transfer_outcome_cg.cp_errortype bin pid_unknown (0x2),
// driven from usb_pie.m.vhdl line 2632. See the sequence header for why MDATA
// is always unexpected on this endpoint configuration.
//
// ENDPOINT CONFIGURATION copied from caliptra_ss_usb_hs_dev_err_pkt_unexpected_test
// (same EP2 ISO IN/OUT slot layout) - see that file for the per-field notes.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_iso_pid_seq_test
//   +usb_errortype_check=1
//   +usb_errortype_check_sel=1
//   +usb_expect_errortype=2
// =============================================================================
class caliptra_ss_usb_hs_dev_err_iso_pid_seq_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_err_iso_pid_seq_test)

    function new(string name = "caliptra_ss_usb_hs_dev_err_iso_pid_seq_test",
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
        // OUT token + MDATA packet against.
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
            caliptra_ss_usb_hs_dev_err_iso_pid_seq_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_ISO_PID_SEQ_TEST_SV

// File contains AI-generated response based on internal company sources
