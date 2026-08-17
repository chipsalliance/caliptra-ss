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

// Records every USB SRAM write while a legacy EP0 checking window is active.
// Firmware snapshots travel over MCI generic wires so the observation
// mechanism never writes the USB SRAM it is checking.
interface caliptra_ss_usb_legacy_ep0_observer_if (
    input  logic        clk,
    input  logic        mem_cs,
    input  logic        mem_web_out,
    input  logic [8:0]  mem_word_addr,
    input  logic [63:0] mem_write_data,
    input  logic [63:0] mem_byte_select,
    input  logic [31:0] fw_snapshot_data,
    input  logic [31:0] fw_snapshot_header,
    output logic [31:0] host_snapshot_ack
);

    localparam int unsigned SNAPSHOT_FIELD_COUNT = 18;
    localparam logic [31:0] SNAPSHOT_VERSION = 32'd1;

    localparam int unsigned SNAPSHOT_FIELD_PUBLISH_SEQUENCE = 0;
    localparam int unsigned SNAPSHOT_FIELD_SETUP_WORD0      = 1;
    localparam int unsigned SNAPSHOT_FIELD_SETUP_WORD1      = 2;
    localparam int unsigned SNAPSHOT_FIELD_EP0_OUT_DESC     = 3;
    localparam int unsigned SNAPSHOT_FIELD_EP0_SETUP_DESC   = 4;
    localparam int unsigned SNAPSHOT_FIELD_EP0_IN_DESC      = 5;
    localparam int unsigned SNAPSHOT_FIELD_EP0_RSVD_DESC    = 6;
    localparam int unsigned SNAPSHOT_FIELD_DEVCMDSTAT       = 7;
    localparam int unsigned SNAPSHOT_FIELD_INTSTAT          = 8;
    localparam int unsigned SNAPSHOT_FIELD_INTEN            = 9;
    localparam int unsigned SNAPSHOT_FIELD_CONFIGURATION    = 10;
    localparam int unsigned SNAPSHOT_FIELD_TRANSFERS        = 11;
    localparam int unsigned SNAPSHOT_FIELD_BUS_RESET_COUNT  = 12;
    localparam int unsigned SNAPSHOT_FIELD_EP0_IRQ_COUNT    = 13;
    localparam int unsigned SNAPSHOT_FIELD_EP0_OUT_COUNT    = 14;
    localparam int unsigned SNAPSHOT_FIELD_EP0_IN_COUNT     = 15;
    localparam int unsigned SNAPSHOT_FIELD_DISPATCH_COUNT   = 16;
    localparam int unsigned SNAPSHOT_FIELD_VERSION          = 17;

    localparam logic [7:0] SNAPSHOT_DATA_MAGIC  = 8'hA5;
    localparam logic [7:0] SNAPSHOT_READY_MAGIC = 8'h5A;
    localparam logic [7:0] SNAPSHOT_ACK_MAGIC   = 8'hC3;

    localparam logic [1:0] SNAPSHOT_STATE_BASELINE = 2'h1;
    localparam logic [1:0] SNAPSHOT_STATE_POST     = 2'h2;
    localparam logic [4:0] SNAPSHOT_READY_FIELD    = 5'h1F;

    typedef struct {
        logic [15:0] generation;
        logic [8:0]  word_address;
        logic [63:0] data;
        logic [7:0]  byte_enable;
    } usb_sram_write_t;

    usb_sram_write_t observed_writes[$];
    logic [31:0] snapshot_fields[0:SNAPSHOT_FIELD_COUNT-1];
    bit          observation_active;
    bit          snapshot_valid;
    logic [15:0] active_generation;
    logic [15:0] snapshot_generation;
    logic [1:0]  snapshot_state;

    function automatic logic [31:0] make_header(
        input logic [7:0]  magic,
        input logic [1:0]  state,
        input logic [4:0]  field_index,
        input logic [15:0] generation);
        return {
            magic,
            state,
            field_index,
            1'b0,
            generation
        };
    endfunction

    function automatic logic [7:0] byte_enable_mask(
        input logic [63:0] byte_select);
        logic [7:0] result;
        for (int unsigned byte_index = 0; byte_index < 8; byte_index++) begin
            result[byte_index] =
                |byte_select[(byte_index * 8) +: 8];
        end
        return result;
    endfunction

    // The SRAM write-enable is active low.
    always @(posedge clk) begin
        if (observation_active && mem_cs && !mem_web_out) begin
            usb_sram_write_t write_item;
            write_item.generation = active_generation;
            write_item.word_address = mem_word_addr;
            write_item.data = mem_write_data;
            write_item.byte_enable =
                byte_enable_mask(mem_byte_select);
            observed_writes.push_back(write_item);
        end
    end

    initial begin
        observation_active = 1'b0;
        snapshot_valid = 1'b0;
        active_generation = '0;
        snapshot_generation = '0;
        snapshot_state = '0;
        host_snapshot_ack = '0;
        observed_writes.delete();
        for (int unsigned field_index = 0;
             field_index < SNAPSHOT_FIELD_COUNT;
             field_index++) begin
            snapshot_fields[field_index] = '0;
        end
    end

    // Receives one complete firmware snapshot. Every field is acknowledged
    // before firmware advances, and the final READY header is published only
    // after firmware has returned to the active EP0 service loop.
    task automatic receive_snapshot(
        input  logic [1:0]  state,
        input  logic [15:0] generation,
        input  time         timeout,
        output bit          found);

        found = 1'b0;
        snapshot_valid = 1'b0;
        host_snapshot_ack = '0;

        fork
            begin
                for (int unsigned field_index = 0;
                     field_index < SNAPSHOT_FIELD_COUNT;
                     field_index++) begin
                    logic [31:0] expected_header;
                    expected_header = make_header(
                        SNAPSHOT_DATA_MAGIC,
                        state,
                        field_index[4:0],
                        generation);
                    wait (fw_snapshot_header == expected_header);
                    snapshot_fields[field_index] =
                        fw_snapshot_data;
                    host_snapshot_ack = make_header(
                        SNAPSHOT_ACK_MAGIC,
                        state,
                        field_index[4:0],
                        generation);
                    wait (fw_snapshot_header != expected_header);
                    host_snapshot_ack = '0;
                end

                wait (fw_snapshot_header == make_header(
                    SNAPSHOT_READY_MAGIC,
                    state,
                    SNAPSHOT_READY_FIELD,
                    generation));
                snapshot_state = state;
                snapshot_generation = generation;
                snapshot_valid = 1'b1;
                found = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable fork;
        host_snapshot_ack = '0;
    endtask

    function automatic bit start_window(input logic [15:0] generation);
        if (!snapshot_valid ||
            (snapshot_state != SNAPSHOT_STATE_BASELINE) ||
            (snapshot_generation != generation)) begin
            $error({"USB legacy EP0 observation window requires a matching ",
                    "generation-qualified baseline snapshot."});
            return 1'b0;
        end
        observed_writes.delete();
        active_generation = generation;
        observation_active = 1'b1;
        return 1'b1;
    endfunction

    function automatic void stop_window();
        observation_active = 1'b0;
    endfunction

    function automatic int unsigned write_count();
        return observed_writes.size();
    endfunction

    function automatic usb_sram_write_t get_write(
        input int unsigned index);
        return observed_writes[index];
    endfunction

    function automatic logic [8:0] get_write_word_address(
        input int unsigned index);
        return observed_writes[index].word_address;
    endfunction

    function automatic logic [63:0] get_write_data(
        input int unsigned index);
        return observed_writes[index].data;
    endfunction

    function automatic logic [7:0] get_write_byte_enable(
        input int unsigned index);
        return observed_writes[index].byte_enable;
    endfunction

    function automatic logic [31:0] get_snapshot_field(
        input int unsigned field_index);
        return snapshot_fields[field_index];
    endfunction

endinterface : caliptra_ss_usb_legacy_ep0_observer_if
