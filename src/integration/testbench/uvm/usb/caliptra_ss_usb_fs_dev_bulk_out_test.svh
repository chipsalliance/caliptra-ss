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

`ifndef CALIPTRA_SS_USB_FS_DEV_BULK_OUT_TEST_SV
`define CALIPTRA_SS_USB_FS_DEV_BULK_OUT_TEST_SV

// =============================================================================
// USB Full-Speed device bulk OUT test.
// DUT is the USB device controller operating as an HS device.
// VIP host (high_speed_capable=1, default) performs HS chirp then sends
// 4096 bytes of bulk OUT data on EP1. MCU firmware verifies word[i]==i.
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_dev_bulk_out_test
// =============================================================================
class caliptra_ss_usb_fs_dev_bulk_out_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_fs_dev_bulk_out_test)

    function new(string name = "caliptra_ss_usb_fs_dev_bulk_out_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // ---------------------------------------------------------------
        // ACC-generated FS conversion block. Puts the VIP into FS-only mode
        // and re-stamps the default endpoints to FS so cfg.is_valid() passes
        // (see claude_md/02_tests.md section 6). Widened FS-link timing knobs
        // keep the link alive through enumeration in scaledown simulation.
        // ---------------------------------------------------------------
        cfg.host_cfg.local_host_cfg.high_speed_capable        = 0;
        cfg.host_cfg.speed                                    = svt_usb_types::FS;
        cfg.dev_cfg.speed                                     = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_FS_BULK_MAX_PACKET_SIZE;
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps (int32-safe, > 1ms FS SOF)
        cfg.dev_cfg.tddis  = 2_000_000_000;
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0; // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;
        cfg.host_cfg.tinactivity = 5_000_000_000.0; // 5 ms in ps
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;
        cfg.host_cfg.drive_reset_time = 150_000_000; // 150 us in ps

        // HS device mode: leave high_speed_capable=1 (default).
        // EP1: BULK OUT at HS, 512-byte max packet.
        // allow_aligned_transfer_without_zero_length=1: the NXP IP_3516 firmware
        // never appends a ZLP after a max-packet-aligned bulk OUT transfer.
        // Without this, the VIP constraint fixed_dev_ep_ustr_valid_ranges forces
        // aligned_transfer_ends_with_zero_length=1, causing the VIP to send a ZLP
        // that the firmware NAKs, eventually ABORTing the transfer after ~1.35ms.
        cfg.dev_cfg.local_device_cfg[0].device_timeout              = 5000us;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction   = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed       = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_FS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].allow_aligned_transfer_without_zero_length = 1;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_dev_bulk_out_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_DEV_BULK_OUT_TEST_SV
