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

`ifndef CALIPTRA_SS_USB_FS_DEV1_DISCONNECT_TEST_SV
`define CALIPTRA_SS_USB_FS_DEV1_DISCONNECT_TEST_SV

// =============================================================================
// USB Full-Speed device disconnect/reconnect test.
// DUT is the USB device controller operating as an FS device. The VIP host
// (high_speed_capable=0) connects at FS, then powers off the port to
// disconnect, waits, then reconnects and verifies the FS link is re-established.
//
// This is the full-speed variant of caliptra_ss_usb_hs_dev_disconnect_test.
// The only functional differences from the HS test are:
//   - The VIP is put into FS-only mode (high_speed_capable=0, host/dev
//     speed=FS) and EP0 CONTROL is re-stamped to FS speed / FS max packet
//     size. Without the EP0 re-stamp the VIP constraint engine generates
//     HS-speed DATA packets that cannot fit the FS link state machine and
//     every SETUP response fires tend_to_end_delay_check.
//   - FS link stability knobs (tddis, tend_to_end_delay_fs, tinactivity,
//     drive_reset_time) are widened so the FS link survives enumeration in
//     scaledown simulation - these are FS link timing requirements, not EP1/EP2
//     traffic configuration.
// The corresponding firmware calls boot_usb_core_fs(), which sets
// DEVCMDSTAT.PFSC (bit 21) to suppress the device K-chirp and keep the link at
// full-speed.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_dev1_disconnect_test
// =============================================================================
class caliptra_ss_usb_fs_dev1_disconnect_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_fs_dev1_disconnect_test)

    function new(string name = "caliptra_ss_usb_fs_dev1_disconnect_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // -----------------------------------------------------------------
        // FS device mode: disable HS chirp so the link negotiates FS. Only
        // EP0 CONTROL is configured - this test exercises enumeration and
        // link events only (no EP1/EP2 data traffic).
        // -----------------------------------------------------------------
        cfg.host_cfg.local_host_cfg.high_speed_capable        = 0;
        cfg.host_cfg.speed                                    = svt_usb_types::FS;
        cfg.dev_cfg.speed                                     = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;

        // Extend device_timeout to allow MCU firmware (software-polled) time to
        // process each SETUP token. The default (shared_cfg) value of 50us is
        // too short for software-polled FS firmware.
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;

        // EP0 CONTROL must be re-stamped to FS speed. setup_usb_20_utmi_host_
        // defaults() leaves this at HS speed / HS max-packet-size; with the FS
        // link negotiated but EP0 still modeled as HS the VIP constraint engine
        // generates HS-speed DATA packets that cannot fit in the FS link state
        // machine, causing every SETUP response to fire tend_to_end_delay_check
        // before firmware is reached.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;

        // endpoint_cfg[1]: EP1 BULK IN. shared_cfg allocates num_endpoints=2 by
        // default and leaves this entry at HS speed / HS bulk max-packet-size
        // (512 bytes). For an FS device that combination is illegal (FS bulk max
        // packet size is 64 bytes), so cfg.is_valid() fails in build_phase
        // before any stimulus runs. This disconnect test drives no EP1 traffic,
        // but the entry still exists and must be re-stamped to FS to pass
        // is_valid().
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_FS_BULK_MAX_PACKET_SIZE;

        // -----------------------------------------------------------------
        // FS link stability knobs. These mirror the proven values from

        // caliptra_ss_usb_fs_dev_bulk_loopback_test and are required for the
        // FS link to survive enumeration in scaledown simulation.
        // -----------------------------------------------------------------

        // tddis: In FS mode the host sends SOF every 1ms. After a SETUP
        // transaction the bus is idle until the next SOF frame. With a small
        // tddis the timer fires during this inter-SOF idle gap and drives
        // DISCONNECTED, aborting the in-progress control transfer. Must be
        // > FS SOF period (1ms). tddis is a signed 32-bit integer in ps units;
        // 2ms (2_000_000_000 ps) fits in int32 and exceeds 1ms SOF.
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps (max int32-safe value > 1ms SOF)
        cfg.dev_cfg.tddis  = 2_000_000_000;

        // tend_to_end_delay_fs: software-polled firmware takes longer than the
        // scaledown default (~1.5 us) to process a SETUP and drive the response
        // at FS. Set to 2ms to safely exceed the FS SOF inter-frame period in
        // scaledown sim (real type, so no int32 overflow).
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0;  // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;

        // tinactivity: the inter-token scheduling gap in an FS control transfer
        // DATA phase can exceed the scaledown default (6.5 us), causing the VIP
        // link SM to fire SUSPENDED and abort the transfer. Widen so the link
        // stays ENABLED through the entire FS enumeration.
        cfg.host_cfg.tinactivity = 5_000_000_000.0;  // 5 ms in ps
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;

        // drive_reset_time: in FS mode with high_speed_capable=0 the VIP host
        // goes directly DISCONNECTED->ENABLED without driving SE0. The NXP
        // IP_3511HS requires a bus reset to enter DEFAULT state (addr=0, EP0
        // armed, UTMI TX enabled). Setting drive_reset_time makes the VIP drive
        // SE0 for this duration before transitioning to ENABLED. 150_000_000 ps
        // = 150 us, well above USB spec tdrst = 10 us.
        cfg.host_cfg.drive_reset_time = 150_000_000;  // 150 us in ps

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_dev1_disconnect_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_DEV1_DISCONNECT_TEST_SV
