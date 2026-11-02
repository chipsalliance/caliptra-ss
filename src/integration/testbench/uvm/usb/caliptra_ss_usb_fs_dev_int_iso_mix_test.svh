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

`ifndef CALIPTRA_SS_USB_FS_DEV_INT_ISO_MIX_TEST_SV
`define CALIPTRA_SS_USB_FS_DEV_INT_ISO_MIX_TEST_SV

// =============================================================================
// USB Full-Speed device mixed INTERRUPT (EP1) + ISOCHRONOUS (EP2) +
// INTERRUPT (EP3) test.
//
// Full-speed counterpart of caliptra_ss_usb_hs_dev_int_iso_mix_test. The
// endpoint map is identical, but the link runs at FS and the sequence drives a
// SINGLE loop of EP1 -> EP2 -> EP3 (the HS twin runs two loops). One loop is
// used here because an FS frame is 1 ms instead of the 125 us HS micro-frame,
// so every transaction costs roughly eight times more simulation time.
//
// endpoint_cfg[] is an array INDEX, not the USB endpoint number:
//   endpoint_cfg[0] ep_number=0 direction=IN  CONTROL      (shared_cfg default)
//   endpoint_cfg[1] ep_number=2 direction=IN  ISOCHRONOUS  FS ISO max packet
//   endpoint_cfg[2] ep_number=2 direction=OUT ISOCHRONOUS  FS ISO max packet
//   endpoint_cfg[3] ep_number=1 direction=IN  INTERRUPT    64 B
//   endpoint_cfg[4] ep_number=1 direction=OUT INTERRUPT    64 B
//   endpoint_cfg[5] ep_number=3 direction=IN  INTERRUPT    64 B
//   endpoint_cfg[6] ep_number=3 direction=OUT INTERRUPT    64 B
// (num_endpoints = 7)
//
// Every endpoint number is fixed at build time and matches the firmware
// (USB_INT_EP=1, USB_ISO_EP=2, USB_INT_EP2=3), so no mid-simulation
// reconfigure() is needed.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_dev_int_iso_mix_test
// =============================================================================

class caliptra_ss_usb_fs_dev_int_iso_mix_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_fs_dev_int_iso_mix_test)

    // Must match USB_INT_EP / USB_ISO_EP / USB_INT_EP2 in the firmware and
    // INT_EP / ISO_EP / INT_EP2 in the sequence.
    localparam int INT_EP      = 1;
    localparam int ISO_EP      = 2;
    localparam int INT_EP2     = 3;
    localparam int INT_MAX_PKT = 64;

    function new(string name = "caliptra_ss_usb_fs_dev_int_iso_mix_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // ---------------------------------------------------------------
        // FS conversion block (same as caliptra_ss_usb_fs_dev_iso_out_test).
        // Puts the VIP into FS-only mode and re-stamps the default endpoints
        // to FS so cfg.is_valid() passes. EP0 in particular must be re-stamped
        // FS or every SETUP trips tend_to_end_delay_check. The widened FS-link
        // timing knobs keep the link alive through enumeration in scaledown
        // simulation:
        //   tddis    must exceed the 1 ms FS SOF period but stay int32-safe
        //   tinactivity must be large or the link SUSPENDs mid control transfer
        //   drive_reset_time is needed because an FS-only VIP host otherwise
        //   goes DISCONNECTED -> ENABLED without SE0, and the NXP IP_3511HS
        //   needs a bus reset to arm EP0.
        // ---------------------------------------------------------------
        cfg.host_cfg.local_host_cfg.high_speed_capable        = 0;
        cfg.host_cfg.speed                                    = svt_usb_types::FS;
        cfg.dev_cfg.speed                                     = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps (int32-safe, > 1ms FS SOF)
        cfg.dev_cfg.tddis  = 2_000_000_000;
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0; // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;
        cfg.host_cfg.tinactivity = 5_000_000_000.0; // 5 ms in ps
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;
        cfg.host_cfg.drive_reset_time = 150_000_000; // 150 us in ps

        // Seven endpoint entries so indices 2..6 are valid.
        cfg.dev_cfg.local_device_cfg[0].num_endpoints   = 7;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5] = new();
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6] = new();

        // slot [1]: EP2 ISO IN (device sends inverse-ramp to host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = ISO_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size  = 0;
        // FS isochronous endpoints must use the FS ISO max packet size (1023).
        // The VIP is_valid() device-interface constraint enforces
        // max_packet_size == SVT_USB_FS_ISOC_MAX_PACKET_SIZE for FS ISO EPs;
        // the HS values (512 IN / 1024 OUT) fail is_valid() at build_phase.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_FS_ISOC_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;

        // slot [2]: EP2 ISO OUT (host sends ramp to device as 2 x 512 B tokens).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = ISO_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::ISOCHRONOUS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].interval        = 1;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_burst_size  = 0;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size = `SVT_USB_FS_ISOC_MAX_PACKET_SIZE;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::FS;

        // slot [3]: EP1 INTERRUPT IN (device -> host loopback).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].ep_number       = INT_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[3].max_packet_size = INT_MAX_PKT;

        // slot [4]: EP1 INTERRUPT OUT (host -> device).
        // allow_aligned_transfer_without_zero_length=1: the firmware never
        // appends a ZLP after a max-packet-aligned transfer (64 % 64 == 0), so
        // without this the VIP would require one and the transfer would ABORT.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].ep_number       = INT_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].max_packet_size = INT_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[4].allow_aligned_transfer_without_zero_length = 1;

        // slot [5]: EP3 INTERRUPT IN (second interrupt endpoint, device -> host).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].ep_number       = INT_EP2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[5].max_packet_size = INT_MAX_PKT;

        // slot [6]: EP3 INTERRUPT OUT (host -> device). Same
        // allow_aligned_transfer_without_zero_length rationale as slot [4].
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].ep_number       = INT_EP2;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].max_packet_size = INT_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[6].allow_aligned_transfer_without_zero_length = 1;

        // Device timeout covers enumeration plus the single EP1 -> EP2 -> EP3
        // loop at FS frame rate, with the same 35 ms budget the FS ISO test
        // uses for its three ISO rounds.
        cfg.dev_cfg.local_device_cfg[0].device_timeout = 35000us;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_dev_int_iso_mix_sequence::type_id::get());

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

`endif // CALIPTRA_SS_USB_FS_DEV_INT_ISO_MIX_TEST_SV
