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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_FS_BULK_LOOPBACK_TEST_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_FS_BULK_LOOPBACK_TEST_SV

// =============================================================================
// USB dual-device Full-Speed bulk loopback test.
//
// Full-speed port of caliptra_ss_usb_dual_device_hs_bulk_loopback_test. The
// topology, firmware and endpoint layout are identical; what changes is the
// negotiated link speed and therefore every speed-dependent VIP knob:
//
//   - high_speed_capable = 0 so the VIP never offers the HS chirp and the link
//     settles at FS (12 Mbit/s). The matching firmware calls
//     boot_usb_core_fs(), which sets DEVCMDSTAT.FORCE_FULLSPEED on BOTH
//     controllers so neither device drives a chirp that would go unanswered.
//   - speed / connected_bus_speed / functionality_support and every
//     endpoint_cfg[].speed are re-stamped to FS, and max_packet_size values
//     switched to the FS constants. Leaving an endpoint at HS while the link is
//     FS makes the VIP constraint engine generate HS-sized DATA packets the FS
//     link state machine cannot carry, which fires tend_to_end_delay_check on
//     every control transfer before firmware is ever reached.
//   - tddis / tend_to_end_delay_fs / tinactivity are widened past the 1 ms FS
//     frame period, and drive_reset_time is set so the VIP drives a real SE0
//     bus reset. See the per-knob comments below; these values are carried over
//     from caliptra_ss_usb_fs_dev1_bulk_loopback_test, where they were tuned
//     against this same firmware stack.
//
// Device topology:
//   - USBDC0 : hub downstream port 1, USB device address 2, PIC vector 3.
//   - USBDC1 : hub downstream port 2, USB device address 3, PIC vector 6
//              (wired via the TB loopback gated by USB_HUB_COMPOUND_DEV1_IRQ).
// Each controller performs an independent EP1 64-byte bulk OUT -> IN loopback.
//
// The SVT VIP models a SINGLE remote device (shared_cfg
// local_device_cfg_size=1). The sequence addresses one controller at a time by
// mutating remote_device_cfg[0].device_address + reconfigure(). The endpoint
// configuration below therefore describes ONE device (EP0 CTRL, EP1 BULK IN,
// EP1 BULK OUT); it is reused for whichever controller is currently addressed.
//
// endpoint_cfg[] is an array INDEX, not the USB endpoint number:
//   endpoint_cfg[0] ep_number=0 direction=IN  CONTROL  (shared_cfg default)
//   endpoint_cfg[1] ep_number=1 direction=IN  BULK IN  (shared_cfg default)
//   endpoint_cfg[2] ep_number=1 direction=OUT BULK OUT (allocated here)
// fix_anchors(dev_idx, ep_array_idx, upstream_idx) uses the array index:
//   Bulk OUT: fix_anchors(0, 2, 0); Bulk IN: fix_anchors(0, 1, 0).
//
// Firmware (caliptra_ss_usb_dual_device_fs_bulk_loopback.c) MUST be built with
// -DUSB_HUB_COMPOUND_DEV1_IRQ and MUST NOT be built with -DUSB_DEV_SEL=1
// (it addresses both apertures at runtime via usb_select_device()).
//
// The actual line speed is not assumed: the test .mk passes
// +usb_fs_speed_check=1, which arms caliptra_ss_usb_fs_speed_checker.sv to
// verify XcvrSelect/TermSelect and the measured RXValid byte period on the UTMI
// interface. The sequence closes that checker's observation window when the
// loopbacks finish.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_dual_device_fs_bulk_loopback_test
// =============================================================================
class caliptra_ss_usb_dual_device_fs_bulk_loopback_test
    extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_dual_device_fs_bulk_loopback_test)

    function new(string name = "caliptra_ss_usb_dual_device_fs_bulk_loopback_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // FS mode: clear the HS capability so the VIP does not drive the HS
        // chirp during bus reset and both sides settle at 12 Mbit/s.
        cfg.host_cfg.local_host_cfg.high_speed_capable        = 0;
        cfg.host_cfg.speed                                    = svt_usb_types::FS;
        cfg.dev_cfg.speed                                     = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;

        // Widen the per-device timeout for the software-polled, interrupt-driven
        // firmware: two controllers are serviced from one polling loop, so a
        // response can be queued behind the other device's servicing.
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;

        // Extend to 3 endpoint entries so index 2 (EP1 BULK OUT) is valid.
        // shared_cfg default allocates 2 ([0]=EP0 CTRL, [1]=EP1 BULK IN).
        cfg.dev_cfg.local_device_cfg[0].num_endpoints   = 3;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();

        // endpoint_cfg[0]: EP0 CONTROL (FS). Must be re-stamped: the host
        // defaults leave EP0 at HS speed and HS max-packet-size, which on an FS
        // link makes the VIP emit DATA packets the FS link SM cannot carry.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size =
            `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;

        // endpoint_cfg[1]: EP1 BULK IN (device sends loopback data to host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_FS_BULK_MAX_PACKET_SIZE;

        // endpoint_cfg[2]: EP1 BULK OUT (host sends data to device).
        // allow_aligned_transfer_without_zero_length=1: the NXP IP_3511
        // firmware never appends a ZLP after a max-packet-aligned bulk OUT.
        // This matters more at FS than at HS: the FS bulk max packet is 64, so
        // the 64-byte loopback payload is exactly aligned and the VIP
        // constraint fixed_dev_ep_ustr_valid_ranges would otherwise force a
        // trailing ZLP that the firmware NAKs, eventually ABORTing the
        // transfer. At HS (max packet 512) the same 64-byte transfer is a short
        // packet and the ZLP never arises.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size =
            `SVT_USB_FS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].allow_aligned_transfer_without_zero_length = 1;

        // tddis: In FS mode the host sends SOF every 1 ms. After a SETUP
        // transaction completes the bus is idle until the next SOF frame, and
        // with the scaledown default of 2 us the tddis timer fires during that
        // inter-SOF gap and drives DISCONNECTED, ABORTing the in-progress
        // control transfer. Must exceed the 1 ms FS frame period.
        // NOTE: tddis is a 32-bit integer in ps units, so the maximum is
        // 2,147,483,647 ps (~2.147 ms). 3 ms would overflow to a negative value
        // the VIP rejects; 2 ms fits and still exceeds the SOF period.
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps
        cfg.dev_cfg.tddis  = 2_000_000_000;

        // tend_to_end_delay_fs: the scaledown preset sets this to ~1.5 us. The
        // interrupt-driven firmware needs far longer than that to decode a
        // SETUP and drive the response, and the VIP protocol scheduler waits
        // for the next SOF boundary before sending the DATA-stage token, so a
        // value at or near the frame period still trips the check just before
        // the token is driven. 2 ms safely clears the FS inter-frame period in
        // scaledown simulation. This is a real type, so the value does not
        // overflow.
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0; // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;

        // tinactivity: the scaledown preset leaves this at 6.5 us. At FS the
        // inter-token scheduling gap inside a control transfer DATA phase can
        // exceed that, which makes the VIP link SM fire SUSPENDED and ABORT the
        // in-flight transfer. 5 ms keeps the link ENABLED through the whole
        // dual enumeration plus both bulk loopbacks.
        cfg.host_cfg.tinactivity = 5_000_000_000.0; // 5 ms in ps
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;

        // drive_reset_time: with high_speed_capable=0 the SVT VIP host goes
        // straight DISCONNECTED->ENABLED without driving SE0. The NXP IP_3511HS
        // requires a bus reset to enter DEFAULT state (addr=0, EP0 armed, UTMI
        // TX enabled), which HS mode gets for free from the mandatory SE0+chirp
        // negotiation. Setting this makes the VIP drive SE0 for the given time
        // before going ENABLED.
        // Units are ps: 150_000_000 ps = 150 us, well above the USB spec tdrst
        // of 10 us. Note 150_000 ps would be only 150 ns, which is NOT long
        // enough for the DUT to register a reset and leaves EP0 uninitialized.
        cfg.host_cfg.drive_reset_time = 150_000_000; // 150 us in ps

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_dual_device_fs_bulk_loopback_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_FS_BULK_LOOPBACK_TEST_SV
