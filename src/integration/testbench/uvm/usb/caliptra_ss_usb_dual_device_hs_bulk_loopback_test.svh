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

`ifndef CALIPTRA_SS_USB_DUAL_DEVICE_HS_BULK_LOOPBACK_TEST_SV
`define CALIPTRA_SS_USB_DUAL_DEVICE_HS_BULK_LOOPBACK_TEST_SV

// =============================================================================
// USB dual-device High-Speed bulk loopback test.
//
// Drives both embedded device controllers of the compound USB IP (IP_3511)
// behind the on-chip 2-port hub:
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
// Firmware (caliptra_ss_usb_dual_device_hs_bulk_loopback.c) MUST be built with
// -DUSB_HUB_COMPOUND_DEV1_IRQ and MUST NOT be built with -DUSB_DEV_SEL=1
// (it addresses both apertures at runtime via usb_select_device()).
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_dual_device_hs_bulk_loopback_test
// =============================================================================
class caliptra_ss_usb_dual_device_hs_bulk_loopback_test
    extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_dual_device_hs_bulk_loopback_test)

    function new(string name = "caliptra_ss_usb_dual_device_hs_bulk_loopback_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode. high_speed_capable defaults to 1 (shared_cfg) so the VIP
        // drives the HS chirp. Widen the HS end-to-end delay threshold for the
        // software-polled, interrupt-driven firmware.
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 5000us;
        cfg.host_cfg.tend_to_end_delay_hs              = 100000000.0; // 100 ms in ns
        cfg.host_cfg.speed                             = svt_usb_types::HS;
        cfg.dev_cfg.speed                              = svt_usb_types::HS;

        // Extend to 3 endpoint entries so index 2 (EP1 BULK OUT) is valid.
        // shared_cfg default allocates 2 ([0]=EP0 CTRL, [1]=EP1 BULK IN).
        cfg.dev_cfg.local_device_cfg[0].num_endpoints   = 3;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();

        // endpoint_cfg[0]: EP0 CONTROL (HS).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size =
            `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;

        // endpoint_cfg[1]: EP1 BULK IN (device sends loopback data to host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;

        // endpoint_cfg[2]: EP1 BULK OUT (host sends data to device).
        // allow_aligned_transfer_without_zero_length=1: the NXP IP_3511 firmware
        // never appends a ZLP after a max-packet-aligned bulk OUT. Without this
        // the VIP constraint fixed_dev_ep_ustr_valid_ranges forces a trailing
        // ZLP the firmware NAKs, eventually ABORTing the transfer.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].allow_aligned_transfer_without_zero_length = 1;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_dual_device_hs_bulk_loopback_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_DUAL_DEVICE_HS_BULK_LOOPBACK_TEST_SV
