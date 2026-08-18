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
        realtime observed_at;
    } packet_record_t;

    protected packet_record_t packet_records[$];
    protected bit active;
    protected logic [15:0] active_generation;
    protected bit stage_trigger_active;
    protected svt_usb_transfer::xfer_stage_enum target_stage;
    protected bit setup_ack_seen;
    protected bit data_stage_started;
    protected bit data_packet_seen;
    protected uvm_event stage_observed;

    function new(
        string name = "caliptra_ss_usb_ocp_arbiter_packet_callback");
        super.new(name);
        active = 1'b0;
        active_generation = '0;
        stage_trigger_active = 1'b0;
        setup_ack_seen = 1'b0;
        data_stage_started = 1'b0;
        data_packet_seen = 1'b0;
        stage_observed = new("stage_observed");
    endfunction

    function void start_window(input logic [15:0] generation);
        packet_records.delete();
        active_generation = generation;
        active = 1'b1;
    endfunction

    function void stop_window();
        active = 1'b0;
        stage_trigger_active = 1'b0;
    endfunction

    function void arm_stage_trigger(
        input svt_usb_transfer::xfer_stage_enum stage);

        target_stage = stage;
        setup_ack_seen = 1'b0;
        data_stage_started = 1'b0;
        data_packet_seen = 1'b0;
        stage_observed.reset();
        stage_trigger_active = 1'b1;
    endfunction

    task wait_for_stage_trigger(
        input time timeout,
        output bit observed);

        observed = 1'b0;
        fork : stage_trigger_timeout
            begin
                stage_observed.wait_trigger();
                observed = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable stage_trigger_timeout;
    endtask

    function int unsigned packet_count();
        return packet_records.size();
    endfunction

    function packet_record_t get_packet(input int unsigned index);
        return packet_records[index];
    endfunction

    function int unsigned count_pid(
        input svt_usb_packet::pid_name_enum pid_name,
        input packet_direction_e direction);

        int unsigned count;
        count = 0;
        foreach (packet_records[index]) begin
            if ((packet_records[index].pid_name == pid_name) &&
                (packet_records[index].direction == direction)) begin
                count++;
            end
        end
        return count;
    endfunction

    function int unsigned count_zlp(input packet_direction_e direction);
        int unsigned count;
        count = 0;
        foreach (packet_records[index]) begin
            if ((packet_records[index].direction == direction) &&
                ((packet_records[index].pid_name == svt_usb_packet::DATA0) ||
                 (packet_records[index].pid_name == svt_usb_packet::DATA1)) &&
                (packet_records[index].data_length == 0)) begin
                count++;
            end
        end
        return count;
    endfunction

    function bit setup_stage_acked();
        bit setup_seen;
        bit setup_data_seen;

        setup_seen = 1'b0;
        setup_data_seen = 1'b0;
        foreach (packet_records[index]) begin
            if ((packet_records[index].direction == PACKET_TX) &&
                (packet_records[index].pid_name == svt_usb_packet::SETUP)) begin
                setup_seen = 1'b1;
                setup_data_seen = 1'b0;
                continue;
            end
            if (setup_seen &&
                (packet_records[index].direction == PACKET_TX) &&
                (packet_records[index].pid_name == svt_usb_packet::DATA0) &&
                (packet_records[index].data_length == 8)) begin
                setup_data_seen = 1'b1;
                continue;
            end
            if (setup_data_seen &&
                (packet_records[index].direction == PACKET_RX) &&
                (packet_records[index].pid_name == svt_usb_packet::ACK)) begin
                return 1'b1;
            end
        end
        return 1'b0;
    endfunction

    function bit get_last_rx_data_length(output int unsigned data_length);
        for (int index = packet_records.size() - 1; index >= 0; index--) begin
            if ((packet_records[index].direction == PACKET_RX) &&
                ((packet_records[index].pid_name == svt_usb_packet::DATA0) ||
                 (packet_records[index].pid_name == svt_usb_packet::DATA1))) begin
                data_length = packet_records[index].data_length;
                return 1'b1;
            end
        end
        data_length = 0;
        return 1'b0;
    endfunction

    function bit get_setup_timestamp(output realtime setup_time);
        bit setup_token_seen;

        setup_token_seen = 1'b0;
        foreach (packet_records[index]) begin
            if (packet_records[index].pid_name == svt_usb_packet::SETUP) begin
                setup_token_seen = 1'b1;
                continue;
            end
            if (setup_token_seen &&
                (packet_records[index].pid_name == svt_usb_packet::DATA0) &&
                (packet_records[index].data_length == 8)) begin
                setup_time = packet_records[index].observed_at;
                return 1'b1;
            end
        end
        setup_time = 0.0;
        return 1'b0;
    endfunction

    function bit legacy_out_stage_completed();
        bit out_token_seen;
        bit out_data_seen;

        out_token_seen = 1'b0;
        out_data_seen = 1'b0;
        foreach (packet_records[index]) begin
            if ((packet_records[index].direction == PACKET_TX) &&
                (packet_records[index].pid_name == svt_usb_packet::OUT)) begin
                out_token_seen = 1'b1;
                out_data_seen = 1'b0;
                continue;
            end
            if (out_token_seen &&
                (packet_records[index].direction == PACKET_TX) &&
                ((packet_records[index].pid_name == svt_usb_packet::DATA0) ||
                 (packet_records[index].pid_name == svt_usb_packet::DATA1))) begin
                out_data_seen = 1'b1;
                continue;
            end
            if (out_data_seen &&
                (packet_records[index].direction == PACKET_RX) &&
                (packet_records[index].pid_name == svt_usb_packet::ACK)) begin
                return 1'b1;
            end
        end
        return 1'b0;
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
        record.data_length = pkt.get_payload_byte_count();
        record.retry_number = pkt.current_retry_number();
        record.observed_at = $realtime;
        packet_records.push_back(record);

        if (!stage_trigger_active) begin
            return;
        end
        if ((direction == PACKET_TX) &&
            (pkt.pid_name == svt_usb_packet::SETUP)) begin
            if (target_stage == svt_usb_transfer::SETUP_STAGE) begin
                stage_trigger_active = 1'b0;
                stage_observed.trigger();
            end
            return;
        end
        if ((direction == PACKET_RX) &&
            (pkt.pid_name == svt_usb_packet::ACK) &&
            !data_stage_started) begin
            setup_ack_seen = 1'b1;
            return;
        end
        if (setup_ack_seen &&
            (direction == PACKET_TX) &&
            (pkt.pid_name == svt_usb_packet::IN) &&
            !data_stage_started) begin
            data_stage_started = 1'b1;
            if (target_stage == svt_usb_transfer::DATA_STAGE) begin
                stage_trigger_active = 1'b0;
                stage_observed.trigger();
            end
            return;
        end
        if (data_stage_started &&
            (direction == PACKET_RX) &&
            ((pkt.pid_name == svt_usb_packet::DATA0) ||
             (pkt.pid_name == svt_usb_packet::DATA1))) begin
            data_packet_seen = 1'b1;
            return;
        end
        if (data_packet_seen &&
            (direction == PACKET_TX) &&
            (pkt.pid_name == svt_usb_packet::OUT) &&
            (target_stage == svt_usb_transfer::STATUS_STAGE)) begin
            stage_trigger_active = 1'b0;
            stage_observed.trigger();
        end
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
