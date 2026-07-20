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

`ifndef CALIPTRA_SS_USB_HS_DEV_ISO_OUT_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_ISO_OUT_TEST_SV

// =============================================================================
// USB High-Speed device isochronous OUT + IN test.
//
// DUT is the USB device controller operating as an HS device.
// VIP host (high_speed_capable=1, default) performs HS chirp, then:
//   Step 5: Sends 1024 bytes of isochronous OUT data on EP2.
//           MCU firmware verifies byte[i] == i % 256 for all 1024 bytes.
//   Step 7: Reads 1024 bytes of isochronous IN data back from EP2.
//           MCU firmware fills EP2 IN buffer with byte[i] = 255-(i%256).
//           VIP sequence verifies the received payload byte-by-byte.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_iso_out_test
//
// Configuration notes (mirrors caliptra_ss_usb_fs_dev_bulk_loopback_test):
//   - setup_usb_20_utmi_host_defaults() allocates 2 slots (indices 0 and 1).
//   - We extend to 3 slots and allocate endpoint_cfg[2] for ISO OUT, keeping
//     slot [1] for ISO IN. This matches the loopback test pattern exactly:
//       slot [0] = EP0  CONTROL (default from shared_cfg)
//       slot [1] = EP2  ISO IN  (direction=IN)
//       slot [2] = EP2  ISO OUT (direction=OUT)
//   - fix_anchors(dev_idx, ep_array_idx, upstream_idx):
//       ISO OUT sequence: fix_anchors(0, 2, 0)
//       ISO IN  sequence: fix_anchors(0, 1, 0)
//   - No direction flip or mid-simulation reconfigure needed; each slot is
//     dedicated to one direction from the start.
// =============================================================================

class caliptra_ss_usb_hs_dev_iso_out_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_iso_out_test)

    function new(string name = "caliptra_ss_usb_hs_dev_iso_out_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // Extend to 3 endpoint_cfg slots (same pattern as loopback test).
        cfg.dev_cfg.local_device_cfg[0].num_endpoints    = 3;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();

        // slot [1]: EP2 ISO IN (device sends inverse-ramp to host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = 512;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;

        // slot [2]: EP2 ISO OUT (host sends ramp to device).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = 2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size = 1024;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::HS;

        // Increase device timeout to give MCU firmware time to process all
        // enumeration SETUP packets, run all 3 ISO rounds, and complete the
        // FRAME_INT test phase.
        // Budget: 3 rounds x ~1.6ms each + inter-round gaps ~2ms + FRAME_INT
        // phase ~2ms poll + VIP-read wait ~1.6ms + printf overhead + margin.
        // 35 ms gives ample headroom for all phases including the 5ms
        // sequence hold after ISO rounds complete.
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 35000us;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_iso_out_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ISO_OUT_TEST_SV
