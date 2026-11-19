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

`ifndef CALIPTRA_SS_USB_HS_DEV_EPINFO_RATE_FEEDBACK_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_EPINFO_RATE_FEEDBACK_TEST_SV

// =============================================================================
// HS EP-info rate-feedback / descriptor-toggle test (suffix
// USB_DMA_EPINFO_RATE_FEEDBACK). Runs
// caliptra_ss_usb_hs_dev_epinfo_rate_feedback_sequence: five 8-byte BULK OUTs
// to USBDC0 EP5, each against a firmware-programmed EP5 OUT descriptor that
// exercises one rate-feedback / toggle-reset leg of usb_dma.m.vhdl.
//
// endpoint_cfg[1] is re-stamped to EP5 BULK OUT so the anchor used by the
// sequence matches the requested endpoint (same reason as
// caliptra_ss_usb_hs_dev_disabled_ep_test: fix_anchors() forces
// endpoint_number == ep_anchor.ep_number).
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_epinfo_rate_feedback_test
// =============================================================================
class caliptra_ss_usb_hs_dev_epinfo_rate_feedback_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_epinfo_rate_feedback_test)

    function new(string name = "caliptra_ss_usb_hs_dev_epinfo_rate_feedback_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 5;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].allow_aligned_transfer_without_zero_length = 1;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_epinfo_rate_feedback_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_EPINFO_RATE_FEEDBACK_TEST_SV

// File contains AI-generated response based on internal company sources
