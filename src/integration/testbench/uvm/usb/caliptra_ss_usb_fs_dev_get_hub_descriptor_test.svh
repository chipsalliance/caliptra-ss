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

`ifndef CALIPTRA_SS_USB_FS_DEV_GET_HUB_DESCRIPTOR_TEST_SV
`define CALIPTRA_SS_USB_FS_DEV_GET_HUB_DESCRIPTOR_TEST_SV

// =============================================================================
// Full-Speed USB GetHubDescriptor test.
//
// Full-speed variant of caliptra_ss_usb_hs_dev_get_hub_descriptor_test: it
// forces the VIP into FS-only mode (high_speed_capable=0) and re-stamps the
// default endpoints to FS so cfg.is_valid() passes, then runs the same
// caliptra_ss_usb_get_hub_descriptor_sequence: enumerate hub + USBDC0, then
// GetHubDescriptor (9-byte Hub Class Descriptor) for the hub. The Hub Class
// Descriptor is speed-independent, so the VIP sequence and the scoreboard
// check (check_hub_descriptor) are reused unchanged from the HS variant.
//
// The accompanying MCU firmware (caliptra_ss_usb_fs_dev_get_hub_descriptor.c)
// uses the interrupt-driven (IRQ) event loop and brings up the USB core with
// boot_usb_core_fs() (sets DEVCMDSTAT.PFSC, bit 21) so the device suppresses
// the K-chirp and the link stays at full speed for the FS-only host VIP.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_dev_get_hub_descriptor_test
// =============================================================================
class caliptra_ss_usb_fs_dev_get_hub_descriptor_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_fs_dev_get_hub_descriptor_test)

    function new(string name = "caliptra_ss_usb_fs_dev_get_hub_descriptor_test",
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

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_get_hub_descriptor_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_DEV_GET_HUB_DESCRIPTOR_TEST_SV
