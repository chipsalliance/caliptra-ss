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

`ifndef CALIPTRA_SS_USB_OCP_DIRECTED_PACKET_SEQUENCE_SVH
`define CALIPTRA_SS_USB_OCP_DIRECTED_PACKET_SEQUENCE_SVH

class caliptra_ss_usb_ocp_directed_packet_sequence
    extends svt_usb_packet_base_sequence;
    `uvm_object_utils(caliptra_ss_usb_ocp_directed_packet_sequence)

    svt_usb_packet::pid_name_enum pid;
    bit [6:0] device_address;
    bit [3:0] endpoint_number;
    bit [7:0] payload_bytes[$];
    bit corrupt_crc;
    svt_usb_configuration packet_configuration;

    function new(string name = "caliptra_ss_usb_ocp_directed_packet_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_packet packet;
        svt_usb_packet_exception exception_item;
        svt_usb_packet::pid_type_enum selected_type;
        svt_usb_packet::pid_name_enum selected_pid;
        svt_usb_packet_exception::crc_error_enum selected_crc;
        svt_usb_payload exact_payload;
        bit [7:0] bytes[];
        bit [6:0] address;
        bit [3:0] endpoint;
        int unsigned byte_count;

        svt_usb_sequence_policy::sequence_policy_pre(sequence_policy);
        selected_pid = pid;
        address = device_address;
        endpoint = endpoint_number;
        case (pid)
            svt_usb_packet::IN, svt_usb_packet::OUT, svt_usb_packet::SETUP:
                selected_type = svt_usb_packet::TOKEN;
            svt_usb_packet::PING:
                selected_type = svt_usb_packet::SPECIAL;
            svt_usb_packet::DATA0, svt_usb_packet::DATA1:
                selected_type = svt_usb_packet::DATA;
            default:
                `uvm_fatal("OCP_PACKET", "Unsupported directed packet PID.")
        endcase
        byte_count = payload_bytes.size();
        if ((selected_type != svt_usb_packet::DATA) && (byte_count != 0))
            `uvm_fatal("OCP_PACKET", "Non-DATA packet cannot carry a payload.")
        bytes = new[byte_count];
        foreach (bytes[i]) bytes[i] = payload_bytes[i];
        packet = new_item("directed_packet");
        if ((packet == null) || (packet_configuration == null))
            `uvm_fatal("OCP_PACKET", "Explicit packet configuration is unavailable.")
        packet.cfg = packet_configuration;
        packet.speed = svt_usb_types::HS;
        if (packet.payload == null)
            packet.payload = new("randomization_payload");
        if (!packet.randomize() with {
                pid_type == local::selected_type;
                pid_name == local::selected_pid;
                device_address == local::address;
                ept_num == local::endpoint;
                payload.byte_count == local::byte_count;
            })
            `uvm_fatal("OCP_PACKET", "Directed packet randomization did not succeed.")
        exact_payload = new("exact_payload");
        if ((byte_count != 0) && !exact_payload.append_bytes(bytes))
            `uvm_fatal("OCP_PACKET", "Could not populate exact packet bytes.")
        packet.payload = exact_payload;
        if (corrupt_crc) begin
            case (pid)
                svt_usb_packet::SETUP:
                    selected_crc = svt_usb_packet_exception::CRC5_ERROR;
                svt_usb_packet::DATA0:
                    selected_crc = svt_usb_packet_exception::CRC16_ERROR;
                default:
                    `uvm_fatal("OCP_PACKET", "CRC injection requires SETUP or DATA0.")
            endcase
            exception_item = new("directed_crc");
            exception_item.cfg = packet.cfg;
            exception_item.xact = packet;
            if (!exception_item.randomize() with {
                    error_group == svt_usb_packet_exception::RANDOM_ERROR_GROUP;
                    error_kind == svt_usb_packet_exception::CRC_ERROR;
                    crc_error == local::selected_crc;
                    mask_or_value == 32'h0000_0001;
                    retry_number == 0;
                    no_exception == 0;
                })
                `uvm_fatal("OCP_PACKET", "CRC injection randomization did not succeed.")
            exception_item.recognized = 0;
            if (packet.exception_list == null)
                packet.exception_list = new("directed_exceptions");
            packet.exception_list.add_exception(exception_item);
            if (!packet.crc_error_detected(1'b1))
                `uvm_fatal("OCP_PACKET", "Injected CRC descriptor was not retained.")
        end
        start_item(packet);
        finish_item(packet);
        svt_usb_sequence_policy::sequence_policy_post(sequence_policy);
    endtask
endclass

`endif
