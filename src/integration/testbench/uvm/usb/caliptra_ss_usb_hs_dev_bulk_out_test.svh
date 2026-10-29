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

`ifndef CALIPTRA_SS_USB_HS_DEV_BULK_OUT_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_BULK_OUT_TEST_SV

// =============================================================================
// USB High-Speed device bulk OUT test.
// DUT is the USB device controller operating as an HS device.
// VIP host (high_speed_capable=1, default) performs HS chirp then sends
// 4096 bytes of bulk OUT data on EP1. MCU firmware verifies word[i]==i.
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_bulk_out_test
// =============================================================================
class caliptra_ss_usb_hs_dev_bulk_out_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_bulk_out_test)

    function new(string name = "caliptra_ss_usb_hs_dev_bulk_out_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS device mode: leave high_speed_capable=1 (default).
        // EP1: BULK OUT at HS, 512-byte max packet.
        // allow_aligned_transfer_without_zero_length=1: the NXP IP_3516 firmware
        // never appends a ZLP after a max-packet-aligned bulk OUT transfer.
        // Without this, the VIP constraint fixed_dev_ep_ustr_valid_ranges forces
        // aligned_transfer_ends_with_zero_length=1, causing the VIP to send a ZLP
        // that the firmware NAKs, eventually ABORTing the transfer after ~1.35ms.
        cfg.dev_cfg.local_device_cfg[0].device_timeout              = 5000us;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction   = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed       = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].allow_aligned_transfer_without_zero_length = 1;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_bulk_out_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_BULK_OUT_TEST_SV
