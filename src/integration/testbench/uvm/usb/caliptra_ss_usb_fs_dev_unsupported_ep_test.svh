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

`ifndef CALIPTRA_SS_USB_FS_DEV_UNSUPPORTED_EP_TEST_SV
`define CALIPTRA_SS_USB_FS_DEV_UNSUPPORTED_EP_TEST_SV

// =============================================================================
// USB Full-Speed "token to an UNSUPPORTED endpoint" test.
//
// Full-speed sibling of caliptra_ss_usb_hs_dev_unsupported_ep_test. DUT is
// USBDC0 behind the on-chip hub, operating as an FS device. After enumeration
// the host VIP sends one 8-byte BULK OUT to EP15, which has no physical
// endpoint behind it because USB_C_DEV0_NBPHYSEP = 28 (14 OUT/IN pairs, so
// only EP1..EP14 are backed). The device must not respond at all.
//
// The endpoint map is speed independent, so the probe endpoint is the same
// EP15 as in the HS variant; only the VIP speed configuration, the bulk max
// packet size (64 instead of 512) and the observation delays change.
//
// See caliptra_ss_usb_fs_dev_unsupported_ep_sequence.svh for the endpoint
// number derivation and the verdict mechanism.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_dev_unsupported_ep_test
// =============================================================================
class caliptra_ss_usb_fs_dev_unsupported_ep_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_fs_dev_unsupported_ep_test)

    function new(string name = "caliptra_ss_usb_fs_dev_unsupported_ep_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
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
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;
        cfg.host_cfg.tddis = 2_000_000_000; // 2 ms in ps (int32-safe, > 1ms FS SOF)
        cfg.dev_cfg.tddis  = 2_000_000_000;
        cfg.host_cfg.tend_to_end_delay_fs = 2_000_000_000.0; // 2 ms in ps
        cfg.dev_cfg.tend_to_end_delay_fs  = 2_000_000_000.0;
        cfg.host_cfg.tinactivity = 5_000_000_000.0; // 5 ms in ps
        cfg.dev_cfg.tinactivity  = 5_000_000_000.0;
        cfg.host_cfg.drive_reset_time = 150_000_000; // 150 us in ps

        // device_timeout at FS follows the other FS tests (5000 us). It must
        // stay LONGER than the sequence's 1000 us silence window so the
        // window, not the VIP, ends the probe; the resulting transfer-level
        // complaint is demoted to informational by the report catcher inside
        // the sequence, and the verdict itself comes from the handshake
        // counter, not the timeout.
        cfg.dev_cfg.local_device_cfg[0].device_timeout        = 5000us;

        // Endpoint config index 1 is the VIP anchor used by the probe
        // transfer: BULK OUT at FS, 64-byte max packet.
        //
        // ep_number MUST be re-stamped to the probe endpoint. The shared
        // default leaves endpoint_cfg[1] as EP1 IN, and svt_usb_transfer's
        // fixed_dev_ep_ustr_valid_ranges constraint forces
        // endpoint_number == ep_anchor.ep_number once fix_anchors() selects
        // this entry. Leaving it at 1 while the sequence asks for 15 makes
        // the solver fail with
        //   (endpoint_number == ep_anchor.ep_number) vs
        //   (endpoint_number == ep_num)
        // The anchor entry and the requested ep_num must agree.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number   = 15;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction   = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type     = svt_usb_types::BULK;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed       = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_FS_BULK_MAX_PACKET_SIZE;
        // The NXP IP_3516 firmware never appends a ZLP after a max-packet
        // aligned bulk OUT, so suppress the VIP's zero-length terminator.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].allow_aligned_transfer_without_zero_length = 1;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_dev_unsupported_ep_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_DEV_UNSUPPORTED_EP_TEST_SV

// File contains AI-generated response based on internal company sources
