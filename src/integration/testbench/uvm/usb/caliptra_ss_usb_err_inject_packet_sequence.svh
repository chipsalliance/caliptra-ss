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

`ifndef CALIPTRA_SS_USB_ERR_INJECT_PACKET_SEQUENCE_SV
`define CALIPTRA_SS_USB_ERR_INJECT_PACKET_SEQUENCE_SV

// =============================================================================
// caliptra_ss_usb_err_inject_packet_sequence
//
// Sends ONE directed USB 2.0 packet on the packet sequencer, optionally with a
// svt_usb_packet_exception attached. The packet layer is the only layer at
// which the VIP accepts a packet exception.
//
// WHY THIS EXISTS (do not re-attach exceptions to a transfer)
//
// The first version of this family attached svt_usb_packet_exception objects
// to svt_usb_transfer.exception_list from a transfer-level hook. That is wrong
// twice over and crashed with a null object access inside the VIP at
// svt_usb_packet_exception.svp line 9846:
//
//   1. WRONG CONTAINER. svt_usb_transfer.exception_list is declared as a
//      svt_usb_transfer_exception_list, which holds svt_usb_transfer_exception
//      objects. That is a different class with a different error model
//      (payload_corrupted_error, invalid_packet_error,
//      control_transfer_format_error, error_val). It has no crc_error,
//      physical_error, length_error or field_id member at all, so none of the
//      wire corruptions this family needs can be expressed there.
//
//   2. UNPOPULATED BACK-REFERENCES. The class reference for
//      svt_usb_packet_exception states that "cfg and xact references must be
//      populated", that "xact must be of type svt_usb_packet", and that xact is
//      "the packet to which this exception is associated". inject() dereferences
//      xact; leaving it null is what produced the crash.
//
// So an exception must be built against a concrete svt_usb_packet and attached
// to THAT packet's exception_list. Both pre-existing users of the framework in
// this repository do exactly that, and this sequence follows them:
//   - caliptra_ss_usb_ocp_directed_packet_sequence.svh lines 92-107
//   - src/usb/tb/sequences/usb_bad_pid_packet_seq.svh lines 45-56
//
// WHY A DIRECTED PACKET IS VALID STIMULUS FOR THESE BINS
//
// cp_errortype in src/usb/coverage/usb_dev_ep_cov.sv samples what the PIE
// reports about a packet it RECEIVED. The PIE cannot tell whether a malformed
// OUT token or DATA packet came from a full host transfer or from a single
// directed packet - it decodes what arrives on the wire. Driving the corrupt
// packet directly is in fact more deterministic than corrupting one packet
// inside a multi-packet transfer, because exactly one packet reaches the DUT
// and exactly one errortype can result.
//
// FIELD MODEL (verified against the class reference, not assumed)
//
//   error_kind is the top-level selector and enables exactly one sub-field:
//     CRC_ERROR           -> crc_error       (CRC5_ERROR, CRC16_ERROR, ...)
//     PHYSICAL_ERROR      -> physical_error  (SYNC_ERROR, EOP_ERROR, ...)
//     LENGTH_ERROR        -> length_error    (SHORT_PACKET_ERROR, LONG_...)
//     PACKET_FIELD_ERROR  -> field_id, with mask_or_value carrying the
//                            REPLACEMENT value (not a corruption mask)
//     PID_CHECK_ERROR and ILLEGAL_DATA_PID_ERROR take no sub-field.
//   error_group == RANDOM_ERROR_GROUP means "no super-category restriction,
//   error_kind is the selector".
//   mask_or_value == 0 is documented as invalid for CRC_ERROR because the value
//   is XORed with the CRC field, so 0 would leave the CRC correct.
//
// VIP LEGALITY CONSTRAINT ON error_kind (read out of the VIP source, not the
// class reference, at sverilog/src/com/svt_usb_packet_exception.svp:3163)
//
//   if (xact.pid_type == svt_usb_packet::DATA)
//     error_kind inside {CRC_ERROR, PHYSICAL_ERROR, ILLEGAL_DATA_PID_ERROR,
//                        PID_CHECK_ERROR, LENGTH_ERROR, NO_OP_ERROR};
//   else if (HANDSHAKE, or SPECIAL with PRE_ERR)
//     error_kind inside {PHYSICAL_ERROR, PACKET_FIELD_ERROR, PID_CHECK_ERROR,
//                        NO_OP_ERROR};
//   else  // TOKEN, SPECIAL/PING, EXT_TOKEN
//     error_kind inside {CRC_ERROR, PHYSICAL_ERROR, PACKET_FIELD_ERROR,
//                        PID_CHECK_ERROR, NO_OP_ERROR};
//
// Consequences this family depends on:
//   - PACKET_FIELD_ERROR is ILLEGAL on a DATA packet. Pinning it there is an
//     unsatisfiable constraint, not a runtime no-op, so use_field is only
//     usable on a TOKEN carrier.
//   - LENGTH_ERROR is legal ONLY on a DATA packet.
//   - CRC_ERROR and PID_CHECK_ERROR are legal on both DATA and TOKEN, so the
//     CRC5-on-OUT-token and PID_CHECK-on-OUT-token injections are in range.
//   - The same block adds "xact.payload.byte_count == 0 -> error_kind !=
//     CRC_ERROR", so a CRC injection needs a non-empty payload.
//
// SENDING WITHOUT AN EXCEPTION
//
// Some PIE error codes are sequencing errors rather than wire corruptions: a
// perfectly well formed packet that simply arrives out of turn. The VIP has no
// error_kind for "valid packet, wrong moment", so for those cases
// attach_exception is cleared and the packet is driven exactly as built.
//
// The use_* bits select which sub-field constraint is applied. SystemVerilog
// cannot assemble an inline constraint block conditionally, so each supported
// combination gets its own randomize() branch.
// =============================================================================
class caliptra_ss_usb_err_inject_packet_sequence
    extends svt_usb_packet_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_err_inject_packet_sequence)

    // ---- what packet to send -------------------------------------------------
    svt_usb_packet::pid_name_enum pid = svt_usb_packet::OUT;
    bit [6:0]                     device_address;
    bit [3:0]                     endpoint_number;
    bit [7:0]                     payload_bytes[$];
    svt_usb_configuration         packet_configuration;

    // ---- which error to inject ----------------------------------------------
    // Clear to send the packet untouched - see "SENDING WITHOUT AN EXCEPTION".
    bit                                      attach_exception = 1'b1;

    svt_usb_packet_exception::error_kind_enum error_kind =
        svt_usb_packet_exception::CRC_ERROR;

    bit                                           use_crc;
    svt_usb_packet_exception::crc_error_enum       crc_sel =
        svt_usb_packet_exception::CRC16_ERROR;

    bit                                           use_phys;
    svt_usb_packet_exception::physical_error_enum  phys_sel =
        svt_usb_packet_exception::SYNC_ERROR;

    // LENGTH_ERROR is legal on a DATA packet only. len_byte_offset is the
    // number of bytes added or removed; it must be non-zero to have an effect.
    bit                                           use_len;
    svt_usb_packet_exception::length_error_enum    len_sel =
        svt_usb_packet_exception::SHORT_PACKET_ERROR;
    int unsigned                                  len_byte_offset = 1;

    // PACKET_FIELD_ERROR: which field, and the value to put there. Legal on a
    // TOKEN packet only, per the valid_ranges constraint quoted above.
    bit                                           use_field;
    svt_usb_packet_exception::field_id_enum        field_sel =
        svt_usb_packet_exception::PID_NAME;
    bit [31:0]                                    field_value;

    // Reported back to the caller so it can tell "injected" from "gave up".
    bit                                           injected;

    string msg_id = "USB_ERR_INJECT_PKT";

    function new(string name = "caliptra_ss_usb_err_inject_packet_sequence");
        super.new(name);
    endfunction

    // -------------------------------------------------------------------------
    // Build the exception against a concrete packet and attach it to that
    // packet's own exception_list.
    // -------------------------------------------------------------------------
    protected function void attach_injected_exception(svt_usb_packet packet);
        svt_usb_packet_exception exc;

        exc      = new("injected_exception");
        exc.cfg  = packet.cfg;
        exc.xact = packet;

        if (use_crc) begin
            if (!exc.randomize() with {
                    error_group   == svt_usb_packet_exception::RANDOM_ERROR_GROUP;
                    error_kind    == local::error_kind;
                    crc_error     == local::crc_sel;
                    // Single bit is enough to make the CRC wrong, and 0 is
                    // documented as invalid here.
                    mask_or_value == 32'h0000_0001;
                    retry_number  == 0;
                    no_exception  == 0;
                })
                `uvm_fatal(msg_id, "CRC exception randomization failed.")
        end
        else if (use_phys) begin
            if (!exc.randomize() with {
                    error_group    == svt_usb_packet_exception::RANDOM_ERROR_GROUP;
                    error_kind     == local::error_kind;
                    physical_error == local::phys_sel;
                    retry_number   == 0;
                    no_exception   == 0;
                })
                `uvm_fatal(msg_id, "Physical exception randomization failed.")
        end
        else if (use_len) begin
            if (!exc.randomize() with {
                    error_group  == svt_usb_packet_exception::RANDOM_ERROR_GROUP;
                    error_kind   == local::error_kind;
                    length_error == local::len_sel;
                    // byte_offset is the number of bytes the packet is
                    // shortened or elongated by, and valid_ranges only bounds
                    // it as >= 0 - an unpinned solve may legally pick 0, which
                    // would leave the packet the correct length and inject
                    // nothing at all.
                    byte_offset  == local::len_byte_offset;
                    retry_number == 0;
                    no_exception == 0;
                })
                `uvm_fatal(msg_id, "Length exception randomization failed.")
        end
        else if (use_field) begin
            if (!exc.randomize() with {
                    error_group   == svt_usb_packet_exception::RANDOM_ERROR_GROUP;
                    error_kind    == local::error_kind;
                    field_id      == local::field_sel;
                    // For PACKET_FIELD_ERROR this is the replacement value.
                    mask_or_value == local::field_value;
                    retry_number  == 0;
                    no_exception  == 0;
                })
                `uvm_fatal(msg_id, "Field exception randomization failed.")
        end
        else begin
            // PID_CHECK_ERROR / ILLEGAL_DATA_PID_ERROR: self-contained kinds.
            if (!exc.randomize() with {
                    error_group  == svt_usb_packet_exception::RANDOM_ERROR_GROUP;
                    error_kind   == local::error_kind;
                    retry_number == 0;
                    no_exception == 0;
                })
                `uvm_fatal(msg_id, "Exception randomization failed.")
        end

        // Generated by us, not recognised from the bus. Assigned after
        // randomize() because randomize() would otherwise overwrite it.
        exc.recognized = 0;

        if (packet.exception_list == null)
            packet.exception_list = new("err_inject_exception_list");
        packet.exception_list.add_exception(exc);
    endfunction

    virtual task body();
        svt_usb_packet               packet;
        svt_usb_packet::pid_type_enum pid_type_sel;
        svt_usb_payload              exact_payload;
        bit [7:0]                    bytes[];
        int unsigned                 byte_count;

        injected = 1'b0;

        // PID to packet-type mapping, same cases the directed OCP sequence
        // supports. Anything else is a coding error in the caller.
        case (pid)
            svt_usb_packet::IN, svt_usb_packet::OUT, svt_usb_packet::SETUP:
                pid_type_sel = svt_usb_packet::TOKEN;
            svt_usb_packet::PING:
                pid_type_sel = svt_usb_packet::SPECIAL;
            svt_usb_packet::DATA0, svt_usb_packet::DATA1:
                pid_type_sel = svt_usb_packet::DATA;
            default:
                `uvm_fatal(msg_id,
                    $sformatf("Unsupported PID %s for error injection.",
                              pid.name()))
        endcase

        // PACKET_FIELD_ERROR on a USB 2.0 DATA packet is rejected by the VIP's
        // own valid_ranges constraint, so catch it here with a readable message
        // instead of letting the solver fail inside the VIP.
        if (attach_exception && use_field &&
            (pid_type_sel == svt_usb_packet::DATA))
            `uvm_fatal(msg_id,
                {"PACKET_FIELD_ERROR is illegal on a non-SuperSpeed DATA ",
                 "packet (svt_usb_packet_exception valid_ranges). Use a TOKEN ",
                 "carrier, or clear attach_exception for a sequencing error."})

        byte_count = payload_bytes.size();
        if ((pid_type_sel != svt_usb_packet::DATA) && (byte_count != 0))
            `uvm_fatal(msg_id,
                "A non-DATA packet cannot carry a payload.")

        bytes = new[byte_count];
        foreach (bytes[i]) bytes[i] = payload_bytes[i];

        packet = new_item("err_inject_packet");
        if ((packet == null) || (packet_configuration == null))
            `uvm_fatal(msg_id,
                "Packet item or packet configuration is unavailable.")

        packet.cfg   = packet_configuration;
        packet.speed = svt_usb_types::HS;

        // The VIP randomizes payload.byte_count, so payload must exist first.
        if (packet.payload == null)
            packet.payload = new("randomization_payload");

        if (!packet.randomize() with {
                pid_type       == pid_type_sel;
                pid_name       == local::pid;
                device_address == local::device_address;
                ept_num        == local::endpoint_number;
                payload.byte_count == local::byte_count;
            })
            `uvm_fatal(msg_id, "Directed packet randomization failed.")

        // Replace the randomized payload with the exact bytes requested, so a
        // failure is reproducible rather than seed-dependent.
        exact_payload = new("exact_payload");
        if ((byte_count != 0) && !exact_payload.append_bytes(bytes))
            `uvm_fatal(msg_id, "Could not populate exact packet bytes.")
        packet.payload = exact_payload;

        if (attach_exception)
            attach_injected_exception(packet);

        `uvm_info(msg_id,
            $sformatf({"Sending %s to addr %0d ep %0d with %0d payload bytes, ",
                       "error_kind=%s."},
                      pid.name(), device_address, endpoint_number, byte_count,
                      attach_exception ? error_kind.name() : "none"), UVM_LOW)

        start_item(packet);
        finish_item(packet);

        injected = 1'b1;
    endtask

endclass

`endif // CALIPTRA_SS_USB_ERR_INJECT_PACKET_SEQUENCE_SV

// File contains AI-generated response based on internal company sources
