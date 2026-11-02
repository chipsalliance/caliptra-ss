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

`ifndef CALIPTRA_SS_USB_HS_DEV1_UNSUPPORTED_EP_TEST_SV
`define CALIPTRA_SS_USB_HS_DEV1_UNSUPPORTED_EP_TEST_SV

// =============================================================================
// USB High-Speed "token to an UNSUPPORTED endpoint" test - USBDC1 variant.
//
// DUT is USBDC1 (the second embedded device controller) behind the on-chip
// hub, operating as an HS device. The host brings up hub downstream port 2
// and enumerates the device, then sends one 8-byte BULK OUT to EP15, which
// has no physical endpoint behind it because USB_C_DEV1_NBPHYSEP = 28 (14
// OUT/IN pairs, so only EP1..EP14 are backed). The device must not respond
// at all.
//
// The endpoint map is identical for both device instances, so the only
// difference against caliptra_ss_usb_hs_dev_unsupported_ep_test is the
// hub port / device selection (sequence side) and the firmware build flag
// -DUSB_DEV_SEL=1 (test-suite side).
//
// See caliptra_ss_usb_hs_dev1_unsupported_ep_sequence.svh for the endpoint
// number derivation and the verdict mechanism.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_dev1_unsupported_ep_test
// =============================================================================
class caliptra_ss_usb_hs_dev1_unsupported_ep_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_dev1_unsupported_ep_test)

    function new(string name = "caliptra_ss_usb_hs_dev1_unsupported_ep_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS device mode: leave high_speed_capable=1 (default).
        // Endpoint config index 1 is the VIP anchor used by the probe
        // transfer: BULK OUT at HS, 512-byte max packet, identical to the
        // caliptra_ss_usb_hs_dev1_bulk_out configuration.
        //
        // device_timeout is kept short (500 us) on purpose. The probe expects
        // no device response, so the VIP transfer times out by design; a long
        // timeout would only stretch the drain after the sequence has already
        // made its decision. The resulting transfer-level complaint is demoted
        // to informational by the report catcher inside the sequence, and the
        // verdict itself comes from the handshake counter, not the timeout.
        cfg.dev_cfg.local_device_cfg[0].device_timeout              = 500us;

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
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed       = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        // The NXP IP_3516 firmware never appends a ZLP after a max-packet
        // aligned bulk OUT, so suppress the VIP's zero-length terminator.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].allow_aligned_transfer_without_zero_length = 1;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_dev1_unsupported_ep_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_DEV1_UNSUPPORTED_EP_TEST_SV

// File contains AI-generated response based on internal company sources
