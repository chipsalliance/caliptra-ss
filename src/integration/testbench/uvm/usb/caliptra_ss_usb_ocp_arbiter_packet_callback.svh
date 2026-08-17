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

`ifndef CALIPTRA_SS_USB_OCP_ARBITER_PACKET_CALLBACK_SV
`define CALIPTRA_SS_USB_OCP_ARBITER_PACKET_CALLBACK_SV

// Captures packet-level evidence for one generation-qualified arbiter
// observation window. The isolation checker uses transfer-level ownership and
// legacy-state invariants; later control-phasing tests reuse these packet
// records to distinguish ACK, NAK, STALL, DATA, and zero-length packets.
class caliptra_ss_usb_ocp_arbiter_packet_callback
    extends svt_usb_link_monitor_callback;

    `uvm_object_utils(caliptra_ss_usb_ocp_arbiter_packet_callback)

    typedef enum bit {
        PACKET_RX,
        PACKET_TX
    } packet_direction_e;

    typedef struct {
        logic [15:0] generation;
        packet_direction_e direction;
        svt_usb_packet::pid_type_enum pid_type;
        svt_usb_packet::pid_name_enum pid_name;
        bit setup_bit;
        bit [6:0] device_address;
        bit [3:0] endpoint_number;
        bit [15:0] data_length;
        int retry_number;
    } packet_record_t;

    protected packet_record_t packet_records[$];
    protected bit active;
    protected logic [15:0] active_generation;

    function new(
        string name = "caliptra_ss_usb_ocp_arbiter_packet_callback");
        super.new(name);
        active = 1'b0;
        active_generation = '0;
    endfunction

    function void start_window(input logic [15:0] generation);
        packet_records.delete();
        active_generation = generation;
        active = 1'b1;
    endfunction

    function void stop_window();
        active = 1'b0;
    endfunction

    function int unsigned packet_count();
        return packet_records.size();
    endfunction

    function packet_record_t get_packet(input int unsigned index);
        return packet_records[index];
    endfunction

    protected function void record_packet(
        input packet_direction_e direction,
        input svt_usb_packet pkt);

        packet_record_t record;

        if (!active || (pkt == null)) begin
            return;
        end

        record.generation = active_generation;
        record.direction = direction;
        record.pid_type = pkt.pid_type;
        record.pid_name = pkt.pid_name;
        record.setup_bit = pkt.get_setup_bit_val();
        record.device_address = pkt.get_device_address_val();
        record.endpoint_number = pkt.ept_num;
        record.data_length = pkt.get_data_length_val();
        record.retry_number = pkt.current_retry_number();
        packet_records.push_back(record);
    endfunction

    virtual function void usb_20_rx_packet_ended(
        svt_usb_link_monitor link_mon,
        svt_usb_packet pkt);
        record_packet(PACKET_RX, pkt);
    endfunction

    virtual function void usb_20_tx_packet_ended(
        svt_usb_link_monitor link_mon,
        svt_usb_packet pkt);
        record_packet(PACKET_TX, pkt);
    endfunction

endclass

`endif // CALIPTRA_SS_USB_OCP_ARBITER_PACKET_CALLBACK_SV
