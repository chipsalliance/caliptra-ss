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

// -----------------------------------------------------------------------------
// Full-Speed variant of caliptra_ss_usb_hs_dev_hub_port_suspend_test.
// Differences from the High-Speed source:
//   - the test puts the VIP into FS-only mode (high_speed_capable=0,
//     FS speeds and FS max-packet sizes) and widens the FS link timing
//     knobs so the link survives enumeration in scaledown simulation;
//   - the firmware poll budget is scaled for the slower link.
// The device controller under test is unchanged (USBDC0).
// -----------------------------------------------------------------------------

`ifndef CALIPTRA_SS_USB_FS_DEV_HUB_PORT_SUSPEND_TEST_SV
`define CALIPTRA_SS_USB_FS_DEV_HUB_PORT_SUSPEND_TEST_SV

// =============================================================================
// USB FS hub downstream PORT_SUSPEND test.
//
// Usage: +UVM_TESTNAME=caliptra_ss_usb_fs_dev_hub_port_suspend_test
//
// This test needs no extra plusargs. In particular it does NOT enable
// caliptra_ss_usb_suspend_resume_checker: per-port suspend actuation is a
// documented and accepted deviation on this IP, so requiring a SuspendM edge
// here would either fail forever or force that shared checker to be relaxed for
// the global_suspend_L2 tests that rely on it as a hard pass/fail. See
// docs/usb_hub_port_suspend_not_wired_report.md.
//
// What this test does verify is the hub port status ladder including write-1-
// clear on C_PORT_SUSPEND, and that the downstream device still answers traffic
// after ClearPortFeature(PORT_SUSPEND). A PASS is therefore not evidence that
// any device suspended. The full reasoning is in the header of
// caliptra_ss_usb_fs_dev_hub_port_suspend_sequence.svh.
// =============================================================================

class caliptra_ss_usb_fs_dev_hub_port_suspend_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_fs_dev_hub_port_suspend_test)

    function new(string name = "caliptra_ss_usb_fs_dev_hub_port_suspend_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
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
            caliptra_ss_usb_fs_dev_hub_port_suspend_sequence::type_id::get());
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_DEV_HUB_PORT_SUSPEND_TEST_SV
