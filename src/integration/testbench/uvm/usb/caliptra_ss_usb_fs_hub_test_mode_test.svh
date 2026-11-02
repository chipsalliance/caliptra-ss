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

`ifndef CALIPTRA_SS_USB_FS_HUB_TEST_MODE_TEST_SV
`define CALIPTRA_SS_USB_FS_HUB_TEST_MODE_TEST_SV

// =============================================================================
// Full-Speed hub SET_FEATURE(DEVICE, TEST_MODE) test.
//
// Full-speed variant of caliptra_ss_usb_hs_hub_test_mode_test. It runs
// caliptra_ss_usb_fs_hub_test_mode_sequence (hub-only enumeration, one rejected
// SET_FEATURE(TEST_MODE) with a random invalid selector 6..255 and one accepted
// SET_FEATURE(TEST_MODE) with a random valid selector 1..5) but forces the VIP
// into FS-only mode and re-stamps the default endpoints to FS so
// cfg.is_valid() passes.
//
// The request under test is decoded entirely in the hub EP0 hardware and that
// decode does not consult the link speed, so the accept/reject behaviour must
// be identical at full speed. Accept/reject is observed on the RTL
// usb_phy_test_mode register through check_phy_test_mode(), i.e. on a probe and
// not over USB - which is what lets the accepted request stand as the last bus
// activity even though it drops the FS link (see the sequence header).
//
// Registered as a Random test in the master test list: the selectors are drawn
// from $urandom_range(), so repeated seeds sweep the selector space.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_hub_test_mode_test
// =============================================================================

class caliptra_ss_usb_fs_hub_test_mode_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_fs_hub_test_mode_test)

    function new(string name = "caliptra_ss_usb_fs_hub_test_mode_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // ---------------------------------------------------------------
        // ACC-generated FS conversion block. Puts the VIP into FS-only mode
        // and re-stamps the default endpoints to FS so cfg.is_valid() passes
        // (see claude_md/02_tests.md section 6). Both default endpoints must
        // be re-stamped even though this test drives no EP1 traffic: the
        // shared cfg stamps EP1 as a 512-byte HS bulk endpoint, which is
        // illegal for an FS device and fails is_valid() on its own. Widened
        // FS-link timing knobs keep the link alive through enumeration in
        // scaledown simulation.
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
            caliptra_ss_usb_fs_hub_test_mode_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_HUB_TEST_MODE_TEST_SV
