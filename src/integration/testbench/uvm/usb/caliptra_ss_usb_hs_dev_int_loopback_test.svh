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

`ifndef CALIPTRA_SS_USB_HS_DEV_INT_LOOPBACK_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_INT_LOOPBACK_TEST_SV

// =============================================================================
// USB High-Speed device INTERRUPT endpoint loopback test.
//
// The DUT device controller arms the selected endpoint as an interrupt
// endpoint (EP entry T=1, RF=1) in the OUT direction, then loops the received
// payload back on the IN direction.
//
// endpoint_cfg[] is an array INDEX, not the USB endpoint number:
//   endpoint_cfg[0] ep_number=0     direction=IN  CONTROL   (shared_cfg default)
//   endpoint_cfg[1] ep_number=INT   direction=IN  INTERRUPT
//   endpoint_cfg[2] ep_number=INT   direction=OUT INTERRUPT (num_endpoints=3)
//
// max_packet_size is 64 bytes: per usb_dma.m.vhdl the "00" maxpacket encoding
// covers FS control/bulk/interrupt and HS control, so the same firmware and
// sequence body are valid at either speed.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_int_loopback_test
// =============================================================================
class caliptra_ss_usb_hs_dev_int_loopback_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_int_loopback_test)

    // Must match USB_INT_EP_FIXED in the firmware and INT_EP_DEFAULT in the
    // sequence for as long as the endpoint number is fixed.
    localparam int INT_EP        = 2;
    localparam int INT_MAX_PKT   = 64;

    function new(string name = "caliptra_ss_usb_hs_dev_int_loopback_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // Widened timing thresholds for software-polled firmware, same values
        // the bulk loopback test needed.
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 5000us;
        cfg.host_cfg.tend_to_end_delay_hs             = 100000000.0; // 100 ms in ns

        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        // Three endpoint entries so index 2 (INTERRUPT OUT) is valid.
        cfg.dev_cfg.local_device_cfg[0].num_endpoints   = 3;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();

        // endpoint_cfg[0]: EP0 CONTROL at HS.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size =
            `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;

        // endpoint_cfg[1]: INTERRUPT IN (device -> host loopback).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = INT_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = INT_MAX_PKT;

        // endpoint_cfg[2]: INTERRUPT OUT (host -> device).
        // allow_aligned_transfer_without_zero_length=1: the firmware never
        // appends a ZLP after a max-packet-aligned transfer (64 % 64 == 0 here),
        // so without this the VIP would require one and the transfer would ABORT.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = INT_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size = INT_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].allow_aligned_transfer_without_zero_length = 1;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_int_loopback_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_INT_LOOPBACK_TEST_SV
