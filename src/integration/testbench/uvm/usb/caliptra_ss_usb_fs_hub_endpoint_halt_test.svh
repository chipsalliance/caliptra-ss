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

`ifndef CALIPTRA_SS_USB_FS_HUB_ENDPOINT_HALT_TEST_SV
`define CALIPTRA_SS_USB_FS_HUB_ENDPOINT_HALT_TEST_SV

// =============================================================================
// Full-Speed hub ENDPOINT_HALT round trip test.
//
// Runs caliptra_ss_usb_fs_hub_endpoint_halt_sequence: hub-only enumeration,
// then GET_STATUS / SET_FEATURE / GET_STATUS / CLEAR_FEATURE / GET_STATUS on
// the hub interrupt IN endpoint (wIndex = 0x0081). The scenario uses control
// transfers only, so the default endpoint configuration of the base test
// (endpoint_cfg[0], EP0 CONTROL) is all that is needed and no extra endpoint
// anchor has to be declared here.
//
// The hub exposes exactly one non-control endpoint, endpoint 1 IN
// (usb_ep_config_hub_pkg.p.vhdl, device 0: EPNB=1, EPDIR=EP_IN, NON_ISO), which
// is why wIndex = 0x0081 is the only meaningful endpoint index. No data traffic
// is driven to it: the Halt state is observed through the GET_STATUS data
// stage, which reads usb_ep_config_handler.reg_ep_stall back through
// epconfig_stall. That decode path is speed independent, which is exactly what
// this full-speed variant exercises.
//
// Full-speed VIP conversion block below is copied from
// caliptra_ss_usb_fs_hub_test_mode_test.svh (itself taken from
// caliptra_ss_usb_fs_dev_get_hub_status_test.svh). Note that BOTH default
// endpoint configurations must be re-stamped to FS even though endpoint_cfg[1]
// carries no traffic in this test: leaving it at the HS max packet size makes
// cfg.is_valid() fail during the build phase.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_hub_endpoint_halt_test
// =============================================================================

class caliptra_ss_usb_fs_hub_endpoint_halt_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_fs_hub_endpoint_halt_test)

    function new(string name = "caliptra_ss_usb_fs_hub_endpoint_halt_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // ---------------------------------------------------------------------
        // Full-speed conversion. high_speed_capable = 0 stops the host VIP from
        // driving the HS chirp handshake, so the link negotiates and stays at
        // full speed. The firmware side pairs with this by calling
        // boot_usb_core_fs(), which sets DEVCMDSTAT.PFSC to suppress the
        // device-side K-chirp.
        // ---------------------------------------------------------------------
        cfg.host_cfg.local_host_cfg.high_speed_capable        = 0;
        cfg.host_cfg.speed                                    = svt_usb_types::FS;
        cfg.dev_cfg.speed                                     = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;

        // Both default endpoints must be re-stamped or cfg.is_valid() fails.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_FS_BULK_MAX_PACKET_SIZE;

        // FS protocol timers. The FS frame period is 1 ms, so the disconnect
        // and inactivity windows must be widened well beyond the HS defaults.
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps (int32-safe, > 1ms FS SOF)
        cfg.dev_cfg.tddis  = 2_000_000_000;
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0; // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;
        cfg.host_cfg.tinactivity = 5_000_000_000.0; // 5 ms in ps
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;
        cfg.host_cfg.drive_reset_time = 150_000_000; // 150 us in ps

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_hub_endpoint_halt_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_HUB_ENDPOINT_HALT_TEST_SV
