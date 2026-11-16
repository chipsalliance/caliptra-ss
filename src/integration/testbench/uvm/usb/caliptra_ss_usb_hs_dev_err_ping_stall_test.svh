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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_PING_STALL_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_PING_STALL_TEST_SV

// =============================================================================
// caliptra_ss_usb_hs_dev_err_ping_stall: PING to a STALLed endpoint, HS, USBDC0.
//
// Stimulus for usb_transfer_outcome_cg.cp_errortype bin sent_stall (0xA), RTL
// site usb_pie.m.vhdl line 2528 (USB_PROT_PING_WF_EP_INFO_VALID). See the
// sequence header for why this is a distinct live site from the one
// caliptra_ss_usb_hs_dev_err_stall already closes.
//
// The EP1 configuration is the same as caliptra_ss_usb_hs_dev_err_stall_test
// - see that file for the per-field notes.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_err_ping_stall_test
// =============================================================================
class caliptra_ss_usb_hs_dev_err_ping_stall_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_err_ping_stall_test)

    function new(string name = "caliptra_ss_usb_hs_dev_err_ping_stall_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable at its default so the VIP chirps.
        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        // EP1 BULK OUT at HS, 512-byte max packet.
        cfg.dev_cfg.local_device_cfg[0].device_timeout            = 5000us;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed     = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].allow_aligned_transfer_without_zero_length = 1;

        // The sequence takes no selector, so it is installed by type.
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_err_ping_stall_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_PING_STALL_TEST_SV

// File contains AI-generated response based on internal company sources
