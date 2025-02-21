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
//
// Description:
//  MCU trace storage
`include "caliptra_sva.svh"


module mci_mcu_trace_buffer 
    import mci_mcu_trace_buffer_pkg::*;
    import trace_buffer_csr_pkg::*;
    #(
    parameter  NUM_TRACE_ENTRIES = 64
    ,parameter DMI_REG_TRACE_RD_PTR_ADDR  = 7'h5D 
    ,localparam NUM_TRACE_ENTRIES_PTR_WIDTH = $clog2(NUM_TRACE_ENTRIES)
    ,localparam TRACE_BUFFER_DWORD_DEPTH = NUM_TRACE_ENTRIES * MCI_MCU_TRACE_PACKET_NUM_DWORDS
    )
    (
    input logic clk,

    // MCI Resets
    input logic rst_b,

    input debug_en,
    
    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if,
    
    // DMI Access
    input logic         dmi_reg_wen,
    input logic [31:0]  dmi_reg_wdata,
    input logic [6:0]   dmi_reg_addr,
    output mci_mcu_trace_buffer_dmi_reg_t dmi_reg,

    // MCU Trace
    input logic [31:0] mcu_trace_rv_i_insn_ip,
    input logic [31:0] mcu_trace_rv_i_address_ip,
    input logic        mcu_trace_rv_i_valid_ip,
    input logic        mcu_trace_rv_i_exception_ip,
    input logic [ 4:0] mcu_trace_rv_i_ecause_ip,
    input logic        mcu_trace_rv_i_interrupt_ip,
    input logic [31:0] mcu_trace_rv_i_tval_ip

);
trace_buffer_csr__in_t trace_buffer_hwif_in;
trace_buffer_csr__out_t trace_buffer_hwif_out;

mci_mcu_trace_buffer_dmi_reg_t dmi_reg_pre_security;

mci_mcu_trace_packet_t  trace_buffer[NUM_TRACE_ENTRIES];
mci_mcu_trace_packet_t  write_trace_data_packet;
mci_mcu_trace_packet_t  read_trace_data_packet;
logic [31:0]            read_trace_data;


logic [31:0] write_ptr; // Entry into trace_buffer array
logic [NUM_TRACE_ENTRIES_PTR_WIDTH-1:0] write_ptr_chop; // Shortened write_ptr
logic [31:0] write_ptr_dword; // Translate write_ptr to num dwords in trace_buffer
logic [31:0] read_ptr; // Entry into trace_buffer array
logic [NUM_TRACE_ENTRIES_PTR_WIDTH-1:0] read_ptr_chop; // Shortened read_ptr
logic [31:0] read_ptr_dword; // Translate read_ptr to num dword in trace_buffer
logic [1:0]  read_ptr_offset; // DWORD Offset in a trace_buffer entry to access
logic write_trace_buffer;
logic trace_buffer_reg_req;
logic trace_buffer_reg_read_error;
logic trace_buffer_reg_write_error;
logic [31:0] c_cpuif_wr_biten; // Byte Enable mapping
logic cif_illegal_access_error;
logic trace_buffer_valid_data;
logic trace_buffer_wrapped;
logic dmi_wr_en_qual;



////////////////////////
// MISC Logic   
////////////////////////
assign trace_buffer_hwif_in.rst_b = rst_b;

assign write_trace_buffer = debug_en && mcu_trace_rv_i_valid_ip;

assign write_trace_data_packet.reserved                  = '0; 
assign write_trace_data_packet.trace_rv_i_interrupt_ip   = mcu_trace_rv_i_interrupt_ip;
assign write_trace_data_packet.trace_rv_i_ecause_ip      = mcu_trace_rv_i_ecause_ip;
assign write_trace_data_packet.trace_rv_i_exception_ip   = mcu_trace_rv_i_exception_ip;
assign write_trace_data_packet.trace_rv_i_tval_ip        = mcu_trace_rv_i_tval_ip;
assign write_trace_data_packet.trace_rv_i_address_ip     = mcu_trace_rv_i_address_ip;
assign write_trace_data_packet.trace_rv_i_insn_ip        = mcu_trace_rv_i_insn_ip;

assign trace_buffer_hwif_in.CONFIG.trace_buffer_depth.next = TRACE_BUFFER_DWORD_DEPTH;

// Reads and writes occur in 1 clock cycles
assign cif_resp_if.hold = '0;


////////////////////////
// Write Pointer
////////////////////////
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        write_ptr <= '0;
        trace_buffer_valid_data <= '0;
        trace_buffer_wrapped <= '0;
    end
    else begin
        if (write_trace_buffer) begin
            trace_buffer_valid_data <= 1'b1;
            if (write_ptr == NUM_TRACE_ENTRIES - 1) begin
                trace_buffer_wrapped <= 1'b1;
                write_ptr <= '0;
            end
            else begin
                write_ptr <= write_ptr + 1;
            end
        end
    end
end
    
// Use appropriate number of bits to fix lint issue.
assign write_ptr_chop = write_ptr[NUM_TRACE_ENTRIES_PTR_WIDTH-1:0];

// Shift left by 2 because there are 4 DWORDs in a trace_buffer entry
// and the data for FW is DWORD accessible. 
assign write_ptr_dword = write_ptr << 2;

assign trace_buffer_hwif_in.WRITE_PTR.ptr.next      = write_ptr_dword; 
assign trace_buffer_hwif_in.STATUS.valid_data.next  = trace_buffer_valid_data; 
assign trace_buffer_hwif_in.STATUS.wrapped.next     = trace_buffer_wrapped; 

////////////////////////
// Read Pointer/Data
////////////////////////

assign read_ptr_dword = trace_buffer_hwif_out.READ_PTR.ptr.value;

// Shift right by 2 because there are 4 DWORDs in a trace_buffer entry
// So div by 4 to get packet number in the trace_buffer. 
assign read_ptr = {2'b00, read_ptr_dword >> 2};

// Use appropriate number of bits to fix lint issue.
assign read_ptr_chop = read_ptr[NUM_TRACE_ENTRIES_PTR_WIDTH-1:0];

// Lower 2 bits are to get the offset within a trace_packet
assign read_ptr_offset = read_ptr_dword[1:0];

// Extracting the correct trace_packet from trace buffer.
assign read_trace_data_packet = trace_buffer[read_ptr_chop];

// Extracting the correct DWORD from the trace_packet.
assign read_trace_data = read_trace_data_packet[read_ptr_offset*32 +: 32];

assign trace_buffer_hwif_in.DATA.data.next = read_trace_data; 

////////////////////////
// Trace Buffer
////////////////////////
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)
        for (int i = 0; i < NUM_TRACE_ENTRIES; i++) begin
            trace_buffer[i] <= '0;
        end
    else begin
        if (write_trace_buffer) begin
            trace_buffer[write_ptr_chop] <= write_trace_data_packet; 
        end
    end
end

////////////////////////
// DMI
////////////////////////


assign dmi_reg_pre_security.TRACE_STATUS = trace_buffer_hwif_out.STATUS;
assign dmi_reg_pre_security.TRACE_CONFIG = trace_buffer_hwif_out.CONFIG;
assign dmi_reg_pre_security.TRACE_WR_PTR = trace_buffer_hwif_out.WRITE_PTR;
assign dmi_reg_pre_security.TRACE_RD_PTR = trace_buffer_hwif_out.READ_PTR;
assign dmi_reg_pre_security.TRACE_DATA   = trace_buffer_hwif_out.DATA; 

assign dmi_reg = debug_en ? dmi_reg_pre_security : '0; 

assign dmi_wr_en_qual = debug_en & dmi_reg_wen;

assign trace_buffer_hwif_in.READ_PTR.ptr.we = dmi_wr_en_qual & (dmi_reg_addr == DMI_REG_TRACE_RD_PTR_ADDR);
assign trace_buffer_hwif_in.READ_PTR.ptr.next = dmi_reg_wdata;


////////////////////////
// CSRs
////////////////////////

// Qualify trace_buffer_reg_req with debug_en
assign trace_buffer_reg_req = cif_resp_if.dv & debug_en;

// Map CIF WSTRB to BITEN of CSR block
genvar i;
generate 
    for (i = 0; i < cif_resp_if.DATA_WIDTH; i = i + 1) begin : map_wstrb_to_biten
        assign c_cpuif_wr_biten[i] = cif_resp_if.req_data.wstrb[i/8];
    end
endgenerate

// Illegal access if CIF tries to access trace_buffer but not in debug mode
assign cif_illegal_access_error = cif_resp_if.dv & ~debug_en;

assign cif_resp_if.error = trace_buffer_reg_read_error | trace_buffer_reg_write_error | cif_illegal_access_error;

trace_buffer_csr i_trace_buffer_csr(
        .clk,
        .rst('0),

        .s_cpuif_req            (trace_buffer_reg_req),
        .s_cpuif_req_is_wr      (cif_resp_if.req_data.write),
        .s_cpuif_addr           (cif_resp_if.req_data.addr[TRACE_BUFFER_CSR_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data        (cif_resp_if.req_data.wdata),
        .s_cpuif_wr_biten       (c_cpuif_wr_biten),
        .s_cpuif_req_stall_wr   (),   
        .s_cpuif_req_stall_rd   (),   
        .s_cpuif_rd_ack         (),   
        .s_cpuif_rd_err         (trace_buffer_reg_read_error),
        .s_cpuif_rd_data        (cif_resp_if.rdata),   
        .s_cpuif_wr_ack         (),     
        .s_cpuif_wr_err         (trace_buffer_reg_write_error),

        .hwif_in(trace_buffer_hwif_in),
        .hwif_out(trace_buffer_hwif_out)
    );
endmodule
