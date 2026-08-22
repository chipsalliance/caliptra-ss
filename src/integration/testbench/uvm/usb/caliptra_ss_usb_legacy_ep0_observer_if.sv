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
    input  logic        utmi_clk,
    input  logic [1:0]  utmi_line_state,
    input  logic        mem_cs,
    input  logic        mem_web_out,
    input  logic [8:0]  mem_word_addr,
    input  logic [63:0] mem_write_data,
    input  logic [63:0] mem_byte_select,
    input  logic [31:0] fw_snapshot_data,
    input  logic [31:0] fw_snapshot_header,
    input  logic        mcu_axi_awvalid,
    input  logic        mcu_axi_awready,
    input  logic        mcu_axi_bvalid,
    input  logic        mcu_axi_bready,
    input  logic        mcu_axi_arvalid,
    input  logic        mcu_axi_arready,
    input  logic        mcu_axi_rvalid,
    input  logic        mcu_axi_rready,
    input  logic        mcu_axi_rlast,
    output logic [31:0] host_snapshot_ack,
    output logic [31:0] host_mcu_command,
    output logic        host_mcu_command_active
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
    localparam logic [7:0] MCU_COMMAND_MAGIC    = 8'hB7;
    localparam logic [7:0] MCU_COMMAND_ACK_MAGIC = 8'hD6;
    localparam logic [3:0] MCU_COMMAND_PUBLISH_BASELINE = 4'h1;
    localparam logic [3:0] MCU_COMMAND_PUBLISH_POST = 4'h2;
    localparam logic [3:0] MCU_COMMAND_RELEASE_CALIPTRA = 4'h3;
    localparam logic [3:0] MCU_COMMAND_PUBLISH_RESET_POST = 4'h4;

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
    int unsigned mcu_axi_writes_outstanding;
    int unsigned mcu_axi_reads_outstanding;
    realtime core_clock_reference;
    realtime core_clock_period;
    realtime utmi_clock_reference;
    realtime utmi_clock_period;
    realtime se0_start_time;

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
        if (core_clock_reference == 0.0) begin
            core_clock_reference = $realtime;
        end else if (core_clock_period == 0.0) begin
            core_clock_period = $realtime - core_clock_reference;
        end

        if (observation_active && mem_cs && !mem_web_out) begin
            usb_sram_write_t write_item;
            write_item.generation = active_generation;
            write_item.word_address = mem_word_addr;
            write_item.data = mem_write_data;
            write_item.byte_enable =
                byte_enable_mask(mem_byte_select);
            observed_writes.push_back(write_item);
        end

        case ({
            mcu_axi_awvalid && mcu_axi_awready,
            mcu_axi_bvalid && mcu_axi_bready
        })
            2'b10: mcu_axi_writes_outstanding++;
            2'b01: begin
                if (mcu_axi_writes_outstanding != 0) begin
                    mcu_axi_writes_outstanding--;
                end
            end
            default: ;
        endcase

        case ({
            mcu_axi_arvalid && mcu_axi_arready,
            mcu_axi_rvalid && mcu_axi_rready && mcu_axi_rlast
        })
            2'b10: mcu_axi_reads_outstanding++;
            2'b01: begin
                if (mcu_axi_reads_outstanding != 0) begin
                    mcu_axi_reads_outstanding--;
                end
            end
            default: ;
        endcase
    end

    always @(posedge utmi_clk) begin
        if (utmi_clock_reference == 0.0) begin
            utmi_clock_reference = $realtime;
        end else if (utmi_clock_period == 0.0) begin
            utmi_clock_period = $realtime - utmi_clock_reference;
        end
    end

    initial begin
        observation_active = 1'b0;
        snapshot_valid = 1'b0;
        active_generation = '0;
        snapshot_generation = '0;
        snapshot_state = '0;
        mcu_axi_writes_outstanding = 0;
        mcu_axi_reads_outstanding = 0;
        core_clock_reference = 0.0;
        core_clock_period = 0.0;
        utmi_clock_reference = 0.0;
        utmi_clock_period = 0.0;
        se0_start_time = 0.0;
        host_snapshot_ack = '0;
        host_mcu_command = '0;
        host_mcu_command_active = 1'b0;
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

        fork : receive_snapshot_timeout
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
                // The MCI register output changes when write data is accepted,
                // before the AXI write response returns. Drain the MCU LSU
                // write channel so ending a test cannot strand the final
                // READY-header response.
                wait (mcu_axi_writes_outstanding == 0);
                snapshot_state = state;
                snapshot_generation = generation;
                snapshot_valid = 1'b1;
                found = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable receive_snapshot_timeout;
        host_snapshot_ack = '0;
    endtask

    function automatic logic [31:0] make_mcu_command(
        input logic [3:0]  opcode,
        input logic [15:0] generation,
        input logic [3:0]  expected_legacy_dispatch_delta);
        return {
            MCU_COMMAND_MAGIC,
            opcode,
            expected_legacy_dispatch_delta,
            generation
        };
    endfunction

    function automatic logic [31:0] make_mcu_command_ack(
        input logic [3:0]  opcode,
        input logic [15:0] generation,
        input logic [3:0]  expected_legacy_dispatch_delta);
        return {
            MCU_COMMAND_ACK_MAGIC,
            opcode,
            expected_legacy_dispatch_delta,
            generation
        };
    endfunction

    // Firmware acknowledges command sampling before performing the requested
    // publication. Holding the command until that acknowledgement prevents a
    // generic-wire pulse from being missed by polling firmware.
    task automatic issue_mcu_command_bounded(
        input  logic [3:0]  opcode,
        input  logic [15:0] generation,
        input  logic [3:0]  expected_legacy_dispatch_delta,
        input  time         timeout,
        output bit          acknowledged);

        logic [31:0] expected_ack;

        acknowledged = 1'b0;
        host_mcu_command = make_mcu_command(
            opcode, generation, expected_legacy_dispatch_delta);
        host_mcu_command_active = 1'b1;
        expected_ack = make_mcu_command_ack(
            opcode, generation, expected_legacy_dispatch_delta);

        fork : mcu_command_ack_timeout
            begin
                wait (fw_snapshot_header === expected_ack);
                acknowledged = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable mcu_command_ack_timeout;

        host_mcu_command_active = 1'b0;
        host_mcu_command = '0;
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

    task automatic wait_launch_phase(input int unsigned phase_index);
        case (phase_index)
            0: @(posedge utmi_clk);
            1: @(negedge utmi_clk);
            2: @(posedge clk);
            3: @(negedge clk);
            4: begin @(posedge utmi_clk); #1ps; end
            5: begin @(negedge utmi_clk); #1ps; end
            6: begin @(posedge clk); #1ps; end
            7: begin @(negedge clk); #1ps; end
            default: @(posedge utmi_clk);
        endcase
    endtask

    task automatic wait_for_mcu_axi_idle(
        input time timeout,
        output bit idle);

        localparam int unsigned QUIET_CYCLES = 4;

        idle = 1'b0;
        fork : mcu_axi_idle_timeout
            begin
                while (!idle) begin
                    bit quiet;

                    wait ((mcu_axi_writes_outstanding == 0) &&
                          (mcu_axi_reads_outstanding == 0));
                    quiet = 1'b1;
                    repeat (QUIET_CYCLES) begin
                        @(negedge clk);
                        if ((mcu_axi_writes_outstanding != 0) ||
                            (mcu_axi_reads_outstanding != 0) ||
                            (mcu_axi_awvalid && mcu_axi_awready) ||
                            (mcu_axi_arvalid && mcu_axi_arready)) begin
                            quiet = 1'b0;
                        end
                    end
                    if (quiet) begin
                        idle = 1'b1;
                    end
                end
            end
            begin
                #(timeout);
            end
        join_any
        disable mcu_axi_idle_timeout;
    endtask

    function automatic bit get_setup_clock_phases(
        input realtime setup_time,
        output time utmi_phase,
        output time core_phase,
        output time utmi_period,
        output time core_period);

        time utmi_elapsed;
        time core_elapsed;
        time utmi_period_time;
        time core_period_time;

        if ((utmi_clock_period == 0.0) || (core_clock_period == 0.0) ||
            (setup_time < utmi_clock_reference) ||
            (setup_time < core_clock_reference)) begin
            utmi_phase = 0;
            core_phase = 0;
            utmi_period = 0;
            core_period = 0;
            return 1'b0;
        end
        utmi_elapsed = time'(setup_time - utmi_clock_reference);
        core_elapsed = time'(setup_time - core_clock_reference);
        utmi_period_time = time'(utmi_clock_period);
        core_period_time = time'(core_clock_period);
        utmi_phase = utmi_elapsed % utmi_period_time;
        core_phase = core_elapsed % core_period_time;
        utmi_period = utmi_period_time;
        core_period = core_period_time;
        return 1'b1;
    endfunction

    function automatic void arm_reset_signal_observation();
        se0_start_time =
            (utmi_line_state == 2'b00) ? $realtime : 0.0;
    endfunction

    task automatic wait_for_reset_signal_bounded(
        input time timeout,
        output bit observed,
        output time duration);

        observed = 1'b0;
        duration = 0;
        fork : reset_signal_timeout
            begin
                if (se0_start_time == 0.0) begin
                    wait (utmi_line_state == 2'b00);
                    se0_start_time = $realtime;
                end
                wait (utmi_line_state != 2'b00);
                duration = time'($realtime - se0_start_time);
                observed = 1'b1;
            end
            begin
                #(timeout);
            end
        join_any
        disable reset_signal_timeout;
        se0_start_time = 0.0;
    endtask

endinterface : caliptra_ss_usb_legacy_ep0_observer_if
