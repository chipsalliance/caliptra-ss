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

`ifndef CALIPTRA_SS_USB_HS_HUB_INT_EP_STATUS_CHANGE_TEST_SV
`define CALIPTRA_SS_USB_HS_HUB_INT_EP_STATUS_CHANGE_TEST_SV

// =============================================================================
// High-Speed hub status-change interrupt endpoint (EP1 IN) polling test.
//
// Runs caliptra_ss_usb_hs_hub_int_ep_status_change_sequence: hub-only
// enumeration, then INTERRUPT IN polls of the hub status-change endpoint across
// three different port change events plus one idle (no-change) poll. Stimulus
// for coverage gap G1 of docs/usb_coverage_gaps.md.
//
// WHY THIS TEST NEEDS ITS OWN ENDPOINT CONFIGURATION
//
// Unlike every other hub test, this one drives DATA traffic at the hub, so the
// VIP must have a model of the hub's interrupt endpoint. do_data_xfer()
// constrains endpoint_number == ep_anchor.ep_number, so without an INTERRUPT IN
// entry the transfer randomize() is inconsistent and the test dies in
// randomize() rather than on the bus.
//
// endpoint_cfg[] is an array INDEX, not the USB endpoint number:
//   endpoint_cfg[0] ep_number=0 direction=IN CONTROL   (shared_cfg default)
//   endpoint_cfg[1] ep_number=1 direction=IN INTERRUPT (overridden here)
//
// Index 1 is reused rather than a third entry being added: the shared
// configuration puts a BULK IN on EP1 there, which this test has no use for,
// and the sequence addresses the endpoint through ep_anchor_idx = 1.
//
// ENDPOINT PARAMETERS, ALL TAKEN FROM THE HUB'S OWN DESCRIPTORS
// (usb_ep0_hub_descr.m.vhdl, ENDPOINT descriptor inside the hub CONFIGURATION
// descriptor, and usb_app_hw_hub.m.vhdl line 437)
//
//   bEndpointAddress 0x81 -> ep_number 1, direction IN
//   bmAttributes     0x03 -> INTERRUPT
//   wMaxPacketSize   0x0001
//   bInterval        0x0C at HS (NOT used as the VIP interval - see
//                    HUB_INT_INTERVAL below for why)
//   hub_epin_buffer_size = ((C_HUB_NB_PORTS+1)/8)+1 = 1 byte
//
// WHY max_packet_size IS DECLARED 64 AND NOT THE DESCRIPTOR'S 1
//
// The hub really does return exactly one byte, and wMaxPacketSize in its
// ENDPOINT descriptor really is 0x0001. This field, however, is the host VIP's
// model of the remote endpoint - it is not a DUT input, and it is not compared
// against the descriptor. The descriptor's wMaxPacketSize is checked
// independently off EP0 by caliptra_ss_usb_data_check_api_impl.
//
// Declaring 1 here is unusable, because it leaves the VIP with no way to decide
// that an IN transfer has finished. A transfer ends either on a short packet or
// on a zero-length terminator. With max_packet_size = 1 a short packet is
// impossible - every one-byte packet is a full packet - and the hub never sends
// a ZLP. Measured consequence: the host issued 4307 IN tokens to addr 1 ep 1
// over 3.75 ms, the hub answered every one of them correctly with the one-byte
// bitmap 0x02 and the host ACKed every one, yet the transfer stayed in state
// ACTIVE and never reported a result. The DUT was never at fault.
//
// Declaring 64 restores the normal rule: the sequence asks for 1 byte, the one
// byte that comes back is a short packet (1 < 64), and the transfer completes on
// the first ACK. No check is weakened - the legs assert the bitmap VALUE the hub
// returns, never the packet geometry. Same reasoning as HUB_INT_INTERVAL below.
//
// allow_aligned_transfer_without_zero_length is deliberately NOT set here.
// All 24 other uses in the repo are on OUT endpoints, where it exists because
// the IP_3511/3516 firmware neither appends nor consumes a ZLP after a
// max-packet-aligned OUT. It says nothing about an IN read.
// caliptra_ss_usb_hs_dev_int_loopback_test is the precedent: it sets the flag on
// its INTERRUPT OUT entry and leaves its INTERRUPT IN entry without it.
//
// NAK RETRY BUDGET IS DELIBERATELY LOWERED HERE
//
// caliptra_ss_usb_shared_cfg raises max_retry_due_to_nak to 500 on every
// endpoint because a software-polled MCU device can NAK for a long time while
// its firmware gets round to the request. The hub endpoint is pure hardware -
// it answers an IN token immediately, with data if a change is pending and with
// NAK if not - so that budget buys nothing here and costs a great deal: the
// sequence's final leg deliberately polls an endpoint that MUST NAK, and at 500
// retries that single transfer would issue 501 tokens.
//
// The budget is therefore cut to HUB_INT_EP_NAK_RETRY on this endpoint only.
// This does not weaken the positive legs: if a change IS pending the hub
// answers the first token, so those legs never consume more than one attempt.
// It bounds only the negative leg.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_hub_int_ep_status_change_test
// =============================================================================

class caliptra_ss_usb_hs_hub_int_ep_status_change_test extends caliptra_ss_usb_base_test;

    `uvm_component_utils(caliptra_ss_usb_hs_hub_int_ep_status_change_test)

    // Hub interrupt endpoint, from the hub ENDPOINT descriptor (bEndpointAddress
    // 0x81) and usb_ep_config_hub_pkg.p.vhdl (EPNB=1, EPDIR=EP_IN, NON_ISO).
    localparam int HUB_INT_EP = 1;

    // Host-side transfer granularity, NOT the descriptor's wMaxPacketSize of 1.
    // The hub returns one byte; declaring 64 makes that one byte a short packet,
    // which is what terminates the transfer. See the header for the measurement
    // that ruled out 1.
    localparam int HUB_INT_MAX_PKT = 64;

    // VIP polling cadence for this endpoint - deliberately NOT the descriptor's
    // bInterval.
    //
    // The hub ENDPOINT descriptor carries bInterval = 0x0C. Every interrupt
    // endpoint in the repo sets this field to 1 regardless of any descriptor
    // value - see caliptra_ss_usb_hs_dev_int_iso_mix_test and
    // caliptra_ss_usb_shared_cfg - and 1 is kept here for the same reason: the
    // test polls on demand, immediately after each port event, and has no
    // interest in reproducing the hub's real service interval.
    //
    // This field is the VIP's own polling period, not a DUT input and not a
    // value that has to agree with the descriptor; the descriptor's bInterval
    // is checked independently off EP0 by caliptra_ss_usb_data_check_api_impl.
    //
    // No check is weakened: the legs assert WHAT the hub returns when a change
    // is or is not pending, never how long the host waited before asking.
    localparam int HUB_INT_INTERVAL = 1;

    // Retry budget for the one leg that is expected to NAK. See the header.
    localparam int HUB_INT_EP_NAK_RETRY = 8;

    function new(string name = "caliptra_ss_usb_hs_hub_int_ep_status_change_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // HS mode: leave high_speed_capable at its default so the VIP chirps.
        cfg.host_cfg.speed = svt_usb_types::HS;
        cfg.dev_cfg.speed  = svt_usb_types::HS;

        // endpoint_cfg[1]: the hub status-change INTERRUPT IN endpoint. The
        // shared configuration left a BULK IN here; it is retargeted rather than
        // a new index being added, because this test has no use for a bulk
        // endpoint on the hub (the hub has none).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = HUB_INT_EP;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::INTERRUPT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = HUB_INT_MAX_PKT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = HUB_INT_INTERVAL;

        // Bound the deliberately-NAKed final leg. Applied AFTER the endpoint
        // fields above and never followed by cfg.apply_nak_retry_budget(), which
        // would put the shared 500 back.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_retry_due_to_nak =
            HUB_INT_EP_NAK_RETRY;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_retry_due_to_nak_before_moving_to_next_ep =
            HUB_INT_EP_NAK_RETRY / 2;

        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_hs_hub_int_ep_status_change_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_HS_HUB_INT_EP_STATUS_CHANGE_TEST_SV
