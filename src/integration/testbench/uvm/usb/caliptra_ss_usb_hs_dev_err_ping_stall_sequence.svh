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

`ifndef CALIPTRA_SS_USB_HS_DEV_ERR_PING_STALL_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_ERR_PING_STALL_SEQUENCE_SV

// =============================================================================
// PING to a STALLed device endpoint on USBDC0 (High Speed).
//
// COVERAGE TARGET
//
// usb_transfer_outcome_cg.cp_errortype, bin sent_stall (0xA), RTL site
// usb_pie.m.vhdl line 2528 (USB_PROT_PING_WF_EP_INFO_VALID, the
// "epinfo_stall = '1' and epinfo_active = '0'" branch reached from a PING
// token). caliptra_ss_usb_hs_dev_err_stall already closes this same code at
// lines 2391/2816 (IN/OUT data to a stalled EP); this test closes the PING
// site specifically, since PING uses its own waiting state in the PIE
// (USB_PROT_PING_WF_EOP / USB_PROT_PING_WF_EP_INFO_VALID) with its own
// assignment of errortype.
//
// FIRMWARE-DRIVEN, SAME AS err_stall
//
// epinfo_stall and epinfo_active are not bus-visible; they are latched
// straight out of the EP1 OUT command/status list entry the firmware writes
// (USB_EP_ENTRY_STALL / USB_EP_ENTRY_ACTIVE). This suite reuses exactly the
// firmware of caliptra_ss_usb_hs_dev_err_stall (STALL set, ACTIVE clear) -
// see that file's .c for the RTL derivation - and only the HOST STIMULUS
// changes: a PING token instead of a bulk OUT.
//
// WHY PING IS A DIRECTED PACKET AND NOT A TRANSFER
//
// PING (HS only) has no svt_usb_transfer counterpart of its own in this
// environment; it is driven as a single directed packet on the packet
// sequencer, exactly like the other members of this family that bypass the
// transfer layer. caliptra_ss_usb_err_inject_packet_sequence already maps
// svt_usb_packet::PING to pid_type SPECIAL and carries no payload, so no
// change to that helper is required.
// =============================================================================

class caliptra_ss_usb_hs_dev_err_ping_stall_sequence
    extends caliptra_ss_usb_err_inject_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_err_ping_stall_sequence)

    string MSG_ID = "USB_ERR_PING_STALL";

    function new(string name = "caliptra_ss_usb_hs_dev_err_ping_stall_sequence");
        super.new(name);
        // No wire corruption: the error comes from the endpoint state the
        // firmware set up, same as err_stall.
        inject_on_label = "";
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        bit                   ok;
        caliptra_ss_usb_err_inject_packet_sequence ping_seq;

        `uvm_info(MSG_ID,
            "Starting PING-to-STALLed-endpoint scenario on EP1.", UVM_LOW)

        err_inject_bringup(host_agent_h, usb_cfg, MSG_ID, ok);
        if (!ok) return;

        ping_seq = caliptra_ss_usb_err_inject_packet_sequence::type_id::create(
            "ping_seq");
        ping_seq.pid                  = svt_usb_packet::PING;
        ping_seq.device_address       = 7'(USBDC0_ADDR);
        ping_seq.endpoint_number      = 4'(EP1_BULK);
        ping_seq.payload_bytes.delete();
        ping_seq.packet_configuration = usb_cfg;
        ping_seq.attach_exception     = 1'b0;
        ping_seq.msg_id               = MSG_ID;

        `uvm_info(MSG_ID,
            $sformatf({"Sending a PING token to addr %0d ep %0d, which the ",
                       "firmware armed with STALL set and ACTIVE clear. A ",
                       "STALL handshake is the expected outcome."},
                      USBDC0_ADDR, EP1_BULK), UVM_LOW)

        ping_seq.start(p_sequencer.usb_20_pkt_sequencer);

        #ERROR_SETTLE_DELAY;

        // No recovery leg: a functional stall persists until the host clears
        // it (USB 2.0 section 8.4.5), and the firmware here deliberately
        // leaves EP1 halted - same as err_stall.
        request_mcu_stop(MSG_ID);

        `uvm_info(MSG_ID,
            "PING-to-STALLed-endpoint scenario complete.", UVM_LOW)
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_DEV_ERR_PING_STALL_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
