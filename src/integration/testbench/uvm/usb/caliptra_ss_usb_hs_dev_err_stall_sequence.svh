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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_STALL_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_STALL_SEQUENCE_SV

// =============================================================================
// Device endpoint STALL on a bulk OUT to USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bin sent_stall (0xA).
//
// WHY THE EXISTING STALL TEST DOES NOT COVER THIS BIN
//
// caliptra_ss_usb_hs_hub_class_req_stall already makes a device STALL a
// control request, but it does it against the HUB: every leg of that sequence
// is a hub CLASS request with recipient BMREQ_OTHER at HUB_ADDR = 1. The PIE
// is instantiated once and time multiplexed, so its pie_errortype is only
// meaningful for whichever function pie_dev_selected currently points at, and
// usb_cov_probe_caliptra_ss.sv instantiates usb_dev_ep_cov for dev0 and dev1
// ONLY - there is no hub instance (see the two instantiations with
// MY_SEL(DEV_SEL_DEV0) and MY_SEL(DEV_SEL_DEV1)). A hub STALL is therefore
// never sampled by this coverpoint, and a DEVICE level STALL is required.
//
// THIS IS NOT AN EXCEPTION INJECTION - IT IS FIRMWARE DRIVEN
//
// The three live assignment sites of 0xA (usb_pie.m.vhdl lines 2391, 2528 and
// 2816) are ALL guarded by the same condition:
//
//     elsif epinfo_stall = '1' and epinfo_active = '0' then
//        -- stall handshake must be returned
//        errortype <= "1010"; --ERROR_SENT_STALL
//
// epinfo_stall and epinfo_active are not bus-visible: usb_dma.m.vhdl lines 303
// and 297 latch them straight out of the endpoint command/status list entry
// the DMA engine fetches,
//
//     epinfo_active <= dma_rdata(31);
//     epinfo_stall  <= dma_rdata(29);
//
// which are exactly USB_EP_ENTRY_ACTIVE and USB_EP_ENTRY_STALL in
// test_suites/libs/usb/usb.h. No amount of wire corruption can set them, so
// there is nothing for svt_usb_packet_exception to do here. The stimulus is
// split:
//
//   firmware  arms EP1 OUT with STALL set and ACTIVE clear, which is the
//             condition above. That is done by the test-suite C file, not here.
//   sequence  sends an ordinary, uncorrupted bulk OUT to EP1 so the device has
//             a transaction to STALL.
//
// WHAT THE HOST SEES
//
// A STALL handshake, which the VIP reports as a transfer that did not succeed.
// As with the corrupted transfers in this family that is the EXPECTED result
// and no status check is run on it. USB 2.0 section 8.4.5 defines STALL as a
// functional stall that persists until the host clears it, so unlike the CRC
// and PID tests there is no clean recovery transfer afterwards: the endpoint
// stays halted by design until a CLEAR_FEATURE, and the firmware in this suite
// deliberately leaves it halted.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_stall_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_stall_sequence)

    string MSG_ID = "USB_ERR_STALL";

    // A full max packet, not a short OUT. do_data_xfer is called with
    // no_zero_length_end(1), which forces aligned_transfer_ends_with_zero_length
    // to 0, and the VIP then requires aligned_transfer == 1 (svt_usb_transfer
    // valid_ranges) which in turn requires the byte count to be a whole
    // multiple of the endpoint max packet size (fixed_dev_ep_ustr_valid_ranges).
    // An earlier 64-byte probe violated that and the solver failed outright
    // rather than shortening the packet. Run time is not a reason to shorten
    // it either: the MCU STOP handshake at the end of body() sets the simtime,
    // not the transfer length. The payload is discarded regardless, because
    // usb_pie.m.vhdl line 2495 sets set_ignore_data while epinfo_stall is high.
    localparam int unsigned STALL_PROBE_BYTES = HS_BULK_MAX_PACKET;

    function new(string name = "caliptra_ss_usb_hs_dev_err_stall_sequence");
        super.new(name);
        // No injection at all: this sequence never calls
        // inject_error_packet(), so nothing is corrupted on the wire. The
        // error comes from the endpoint state the firmware set up. The label
        // is left empty because there is no injection leg to name.
        inject_on_label = "";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_transfer      req;
        bit [7:0]             data[];
        bit                   ok;

        `uvm_info(MSG_ID,
            "Starting device endpoint STALL scenario on EP1 bulk OUT.", UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        data = new[STALL_PROBE_BYTES];
        foreach (data[i]) data[i] = i[7:0];

        `uvm_info(MSG_ID,
            $sformatf({"BULK OUT of %0d bytes to addr %0d EP%0d, which the ",
                       "firmware armed with STALL set and ACTIVE clear. A ",
                       "STALL handshake is the expected outcome."},
                      STALL_PROBE_BYTES, USBDC0_ADDR, EP1_BULK), UVM_LOW)

        do_data_xfer(
            .agent_h            (host_agent_h),
            .usb_cfg            (usb_cfg),
            .xfer_kind          (svt_usb_transfer::BULK_OUT_TRANSFER),
            .device_addr        (USBDC0_ADDR),
            .ep_num             (EP1_BULK),
            .byte_count         (STALL_PROBE_BYTES),
            .ep_anchor_idx      (EP1_ANCHOR),
            .label              ("HS_BULK_OUT_EP1_STALLED"),
            .req                (req),
            .payload_data       (data),
            .no_zero_length_end (1));

        #ERROR_SETTLE_DELAY;

        // Release the MCU. These firmware images have no completion event
        // of their own - a corrupted packet is meant to be discarded - so
        // without this they poll to USB_ERR_POLL_TIMEOUT and the simtime is
        // set by that loop count rather than by the stimulus. See
        // request_mcu_stop() in caliptra_ss_usb_err_inject_base_sequence.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID, "Device endpoint STALL scenario complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_STALL_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
