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

`ifndef CALIPTRA_SS_USB_FS_DEV_BULK_LOOPBACK_TEST_SV
`define CALIPTRA_SS_USB_FS_DEV_BULK_LOOPBACK_TEST_SV

// =============================================================================
// USB Full-Speed device bulk loopback test.
// DUT is the USB device controller operating as an FS device.
// VIP host (high_speed_capable=0) operates in FS mode and:
//   1. Enumerates the DUT device.
//   2. Sends 64 bytes of bulk OUT data on EP1 (host -> device).
//   3. Reads 64 bytes back from EP1 IN (device -> host loopback).
// MCU firmware copies EP1 OUT data to EP1 IN buffer and signals completion.
//
// endpoint_cfg[] is an array INDEX, not the USB endpoint number:
//   endpoint_cfg[0] ep_number=0 direction=IN  CONTROL  (allocated by shared_cfg default)
//   endpoint_cfg[1] ep_number=1 direction=IN  BULK IN  (allocated by shared_cfg default)
//   endpoint_cfg[2] ep_number=1 direction=OUT BULK OUT (allocated here, num_endpoints=3)
// fix_anchors(dev_idx, ep_array_idx, upstream_idx) must use the array index:
//   Bulk OUT sequence: fix_anchors(0, 2, 0)
//   Bulk IN  sequence: fix_anchors(0, 1, 0)
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_dev_bulk_loopback_test
// =============================================================================
class caliptra_ss_usb_fs_dev_bulk_loopback_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_fs_dev_bulk_loopback_test)

    function new(string name = "caliptra_ss_usb_fs_dev_bulk_loopback_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // FS device mode: disable HS chirp so the link negotiates FS.
        cfg.host_cfg.local_host_cfg.high_speed_capable                = 0;
        cfg.host_cfg.speed                                            = svt_usb_types::FS;
        cfg.dev_cfg.speed                                             = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support         = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].device_timeout                = 5000us;

        // Extend to 3 endpoint entries so index 2 (BULK OUT) is valid.
        // shared_cfg default allocates 2 entries ([0]=EP0 CTRL, [1]=EP1 IN).
        // For loopback we need index 2 for EP1 OUT as well.
        cfg.dev_cfg.local_device_cfg[0].num_endpoints                 = 3;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2]               = new();

        // endpoint_cfg[0]: EP0 CONTROL - must be re-stamped to FS speed.
        // setup_usb_20_utmi_host_defaults() leaves this at HS speed and
        // HS max-packet-size. With FS link negotiated but EP0 still modeled
        // as HS the VIP constraint engine generates HS-speed DATA packets
        // that cannot fit in the FS link state machine, causing every SETUP
        // response to fire tend_to_end_delay_check before firmware is reached.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;

        // endpoint_cfg[1]: EP1 BULK IN (device sends loopback data to host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number     = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction     = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type       = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed         = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_FS_BULK_MAX_PACKET_SIZE;

        // endpoint_cfg[2]: EP1 BULK OUT (host sends data to device).
        // allow_aligned_transfer_without_zero_length=1: the NXP IP_3516 firmware
        // never appends a ZLP after a max-packet-aligned bulk OUT transfer.
        // Without this the VIP constraint fixed_dev_ep_ustr_valid_ranges forces
        // aligned_transfer_ends_with_zero_length=1, causing the VIP to send a ZLP
        // that the firmware NAKs, eventually ABORTing the transfer.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number     = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction     = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type       = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed         = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size =
            `SVT_USB_FS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].allow_aligned_transfer_without_zero_length = 1;

        // tddis: In FS mode the host sends SOF every 1ms. After a SETUP
        // transaction completes the bus is idle until the next SOF frame
        // (~1ms later). With the scaledown default of 2us the tddis timer
        // fires during this inter-SOF idle gap and drives DISCONNECTED,
        // ABORTing the in-progress control transfer.
        // Must be > FS SOF period (1ms).
        // NOTE: tddis is a 32-bit integer in ps units. The maximum value
        // that fits in a signed 32-bit integer is 2,147,483,647 ps (~2.147ms).
        // 3ms would overflow to a negative value which the VIP rejects.
        // Use 2ms (2_000_000_000 ps) which fits in int32 and exceeds 1ms SOF.
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps units (max int32-safe value > 1ms SOF)
        cfg.dev_cfg.tddis  = 2_000_000_000;

        // The scaledown preset sets tend_to_end_delay_fs to ~1.5 us. The NXP
        // IP_3516 firmware (ISR-driven) takes longer than 1.5 us to process a
        // SETUP token and drive the response at FS. Extend tend_to_end_delay_fs
        // to 500 us so firmware has adequate response time and the VIP link-layer
        // tend_to_end_delay_check does not fire on every control transfer.
        // In scaledown simulation the FS SOF period is ~500us (not 1ms real-time).
        // The VIP protocol scheduler waits until the next SOF boundary before sending
        // the DATA stage IN token for a CONTROL transfer. With tend_to_end_delay_fs=500us
        // the timer fires at exactly the SOF boundary (500us after SETUP EOP), just
        // nanoseconds before the VIP sends the token, triggering tend_to_end_delay_check.
        // Set to 2ms to safely exceed the FS SOF inter-frame period in scaledown sim.
        // tend_to_end_delay_fs is a real type so 2_000_000_000.0 does not overflow.
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0;  // 2 ms in ps units
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;

        // tinactivity: The scaledown preset leaves tinactivity at 6.5 us. At FS
        // speed the inter-token scheduling gap within a control transfer DATA phase
        // can exceed 6.5 us, causing the VIP link SM to fire SUSPENDED, which ABORTs
        // any in-progress transfer. Set to 5 ms so the link stays ENABLED through
        // the entire FS enumeration and bulk transfer sequence.
        cfg.host_cfg.tinactivity = 5_000_000_000.0;  // 5 ms in ps units
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;

        // drive_reset_time: In FS mode with high_speed_capable=0 the SVT VIP
        // host goes directly DISCONNECTED->ENABLED without driving SE0. The NXP
        // IP_3511HS requires a bus reset to enter DEFAULT state (addr=0, EP0 armed,
        // UTMI TX enabled). Setting drive_reset_time makes the VIP autonomously
        // drive SE0 for this duration BEFORE transitioning to ENABLED, exactly as
        // HS mode does via mandatory SE0+chirp negotiation in the USB 2.0 spec.
        // Units are ps: 150_000_000 ps = 150 us, well above USB spec tdrst = 10 us.
        // NOTE: 150000 ps = only 150 ns -- that is NOT enough for the DUT to register
        // a bus reset. The value must be 150_000_000 (150 us) for EP0 to be initialized.
        cfg.host_cfg.drive_reset_time = 150_000_000;  // 150 us in ps units (150_000_000 ps)

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_dev_bulk_loopback_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_DEV_BULK_LOOPBACK_TEST_SV
