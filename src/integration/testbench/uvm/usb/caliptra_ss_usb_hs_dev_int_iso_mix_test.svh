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

`ifndef CALIPTRA_SS_USB_HS_DEV_INT_ISO_MIX_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV_INT_ISO_MIX_TEST_SV

// =============================================================================
// USB High-Speed device mixed INTERRUPT (EP1) + ISOCHRONOUS (EP2) +
// INTERRUPT (EP3) test.
//
// Combines caliptra_ss_usb_hs_dev_int_loopback_test and
// caliptra_ss_usb_hs_dev_iso_out_test into one simulation: two INTERRUPT
// endpoints (EP1, EP3) and one ISOCHRONOUS endpoint (EP2) are modeled and
// armed, and the sequence accesses them in the order EP1 -> EP2 -> EP3, and it
// repeats that whole EP1 -> EP2 -> EP3 order twice (two loops). The timing
// budgets below are therefore doubled with respect to the single-loop version.
//
// endpoint_cfg[] is an array INDEX, not the USB endpoint number:
//   endpoint_cfg[0] ep_number=0 direction=IN  CONTROL      (shared_cfg default)
//   endpoint_cfg[1] ep_number=2 direction=IN  ISOCHRONOUS  512 B
//   endpoint_cfg[2] ep_number=2 direction=OUT ISOCHRONOUS  1024 B
//   endpoint_cfg[3] ep_number=1 direction=IN  INTERRUPT    64 B
//   endpoint_cfg[4] ep_number=1 direction=OUT INTERRUPT    64 B
//   endpoint_cfg[5] ep_number=3 direction=IN  INTERRUPT    64 B
//   endpoint_cfg[6] ep_number=3 direction=OUT INTERRUPT    64 B
// (num_endpoints = 7)
//
// Slots [1]/[2] keep the exact indices the proven ISO test used so the ISO
// anchor behaviour is unchanged; the two INTERRUPT pairs are appended at
// [3]/[4] (EP1) and [5]/[6] (EP3). No mid-simulation reconfigure() is needed:
// every endpoint number is fixed at build time and matches the firmware
// (USB_INT_EP=1, USB_ISO_EP=2, USB_INT_EP2=3).
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev_int_iso_mix_test
// =============================================================================

class caliptra_ss_usb_hs_dev_int_iso_mix_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev_int_iso_mix_test)

    // Must match USB_INT_EP / USB_ISO_EP in the firmware and INT_EP / ISO_EP in
    // the sequence.
    localparam int INT_EP          = 1;
    localparam int ISO_EP          = 2;
    localparam int INT_EP2         = 3;
    localparam int INT_MAX_PKT     = 64;
    localparam int ISO_IN_MAX_PKT  = 512;
    localparam int ISO_OUT_MAX_PKT = 1024;

    function new(string name = "caliptra_ss_usb_hs_dev_int_iso_mix_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        // Seven endpoint entries so indices 2..6 are valid.
        cfg.dev_cfg.local_device_cfg[0].num_endpoints   = 7;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6] = new();

        // slot [0]: EP0 CONTROL at HS.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size =
            `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;

        // slot [1]: EP2 ISO IN (device sends inverse-ramp to host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = ISO_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = ISO_IN_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;

        // slot [2]: EP2 ISO OUT (host sends ramp to device).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = ISO_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size = ISO_OUT_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::HS;

        // slot [3]: EP1 INTERRUPT IN (device -> host loopback).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].ep_number       = INT_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].max_packet_size = INT_MAX_PKT;

        // slot [4]: EP1 INTERRUPT OUT (host -> device).
        // allow_aligned_transfer_without_zero_length=1: the firmware never
        // appends a ZLP after a max-packet-aligned transfer (64 % 64 == 0), so
        // without this the VIP would require one and the transfer would ABORT.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].ep_number       = INT_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].max_packet_size = INT_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].allow_aligned_transfer_without_zero_length = 1;

        // slot [5]: EP3 INTERRUPT IN (second interrupt endpoint, device -> host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].ep_number       = INT_EP2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].max_packet_size = INT_MAX_PKT;

        // slot [6]: EP3 INTERRUPT OUT (host -> device). Same
        // allow_aligned_transfer_without_zero_length rationale as slot [4].
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].ep_number       = INT_EP2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].max_packet_size = INT_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].allow_aligned_transfer_without_zero_length = 1;

        // Timing thresholds: union of what the two source tests needed. The ISO
        // test needed a 35 ms device_timeout for its long software-polled
        // phases; the INTERRUPT test needed the widened end-to-end delay so a
        // software-polled IN is not declared a response timeout.
        // Both budgets are doubled because the sequence now runs two loops of
        // the EP1 -> EP2 -> EP3 phase order.
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 70000us;
        cfg.host_cfg.tend_to_end_delay_hs             = 200000000.0; // 200 ms in ns

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev_int_iso_mix_sequence::type_id::get());

        // Endpoints allocated above are created after shared_cfg has already
        // run, so they still carry the VIP default max_retry_due_to_nak of
        // 10 (1 attempt + 10 retries = 11 NAKs, then the transfer is marked
        // ABORTED with an all-zero results_status). Re-apply the shared
        // budget now that every endpoint object exists. This MUST be the last
        // statement in build_phase.
        cfg.apply_nak_retry_budget();

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_INT_ISO_MIX_TEST_SV
