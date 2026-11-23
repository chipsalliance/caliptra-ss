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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_MISSING_DATA_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_MISSING_DATA_SEQUENCE_SV

// =============================================================================
// Missing DATA packet after a bulk OUT token to USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bin timeout (0x6), RTL site
// usb_pie.m.vhdl line 2442: "TIMEOUT: Data Packet or epinfo_valid is not
// received on time" after an OUT/SETUP token has been accepted for an armed
// endpoint. This is a different live site of 0x6 from the ones already
// covered elsewhere in the regression (host IN with no device data, etc.);
// this one specifically needs a lone OUT token with no following data at
// all.
//
// WHY A BARE DIRECTED TOKEN AND NOT A TRANSFER
//
// A svt_usb_transfer always supplies the DATA phase itself; there is no VIP
// knob to "send the token and then nothing" at the transfer layer. The only
// way to put a lone token on the wire is the packet sequencer, exactly as
// the rest of this family uses for its injected packets -
// caliptra_ss_usb_err_inject_packet_sequence with attach_exception cleared,
// since this is not a wire corruption at all: the token itself is perfectly
// formed, the only fault is that nothing follows it.
//
// WHY THE WAIT IS LONGER THAN THE RTL'S OWN TIMER
//
// usb_pie.m.vhdl's MAX_PACKET_HANDLING_TIMER is PACKET_EVENT_TIMEOUT_HS = 127
// (bit periods at the internal packet-handling clock), which retires in well
// under a microsecond of simulation time. TIMEOUT_WAIT below is a large
// margin over that so the PIE has unambiguously reached its own timeout
// before the sequence moves on, independent of the exact internal clock
// ratio.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_missing_data_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_missing_data_sequence)

    string MSG_ID = "USB_ERR_MISSING_DATA";

    // Generous margin over usb_pie.m.vhdl's MAX_PACKET_HANDLING_TIMER
    // (PACKET_EVENT_TIMEOUT_HS = 127 internal ticks), which is far shorter
    // than this in wall sim time. See header.
    localparam realtime TIMEOUT_WAIT = 100us;

    function new(string name = "caliptra_ss_usb_hs_dev_err_missing_data_sequence");
        super.new(name);
        inject_on_label = "HS_BULK_OUT_EP1_TOKEN_NO_DATA";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;
        caliptra_ss_usb_err_inject_packet_sequence tok_seq;

        `uvm_info(MSG_ID,
            "Starting missing-DATA-packet scenario on EP1 bulk OUT.", UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_pre_clean", MSG_ID);

        // The lone OUT token: well formed, no exception, and deliberately
        // not followed by any DATA packet.
        tok_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            "tok_seq");
        tok_seq.pid                  = svt_usb_packet::OUT;
        tok_seq.device_address       = 7'(USBDC0_ADDR);
        tok_seq.endpoint_number      = 4'(EP1_BULK);
        tok_seq.payload_bytes.delete();
        tok_seq.packet_configuration = usb_cfg;
        tok_seq.attach_exception     = 1'b0;
        tok_seq.msg_id                = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf({"%s: sending a lone OUT token to addr %0d ep %0d with ",
                       "no following DATA packet. The PIE's packet-handling ",
                       "timer must expire."},
                      inject_on_label, USBDC0_ADDR, EP1_BULK), UVM_LOW)

        tok_seq.start(p_sequencer.usb_20_pkt_sequencer);

        // Let the PIE's internal timer expire well before moving on.
        #TIMEOUT_WAIT;

        do_clean_reference_xfer(host_agent_h, usb_cfg,
                                "HS_BULK_OUT_EP1_post_clean", MSG_ID);

        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "Missing-DATA-packet scenario complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_MISSING_DATA_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
