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

`include "soc_address_map_defines.svh"
`include "soc_address_map_field_defines.svh"

module caliptra_ss_top_tb_soc_bfm
import axi_pkg::*;
import mci_dmi_pkg::*;
import mci_reg_pkg::*;
import mci_pkg::*;
import soc_ifc_pkg::*;
import mcu_mbox_csr_pkg::*;
import trace_buffer_csr_pkg::*;
#(
    parameter MCU_SRAM_SIZE_KB = 512
) 
(
    input logic core_clk,
    output logic                       cptra_pwrgood,
    output logic                       cptra_rst_b,
    //output logic                       BootFSM_BrkPoint,
    input int                          cycleCnt,

    output logic [31:0] cptra_ss_strap_mcu_lsu_axi_user_i,
    output logic [31:0] cptra_ss_strap_mcu_ifu_axi_user_i,
    output logic [31:0] cptra_ss_strap_mcu_sram_config_axi_user_i,
    output logic [31:0] cptra_ss_strap_mci_soc_config_axi_user_i,
    output logic [31:0] cptra_ss_strap_caliptra_dma_axi_user_i,

    output logic         cptra_ss_mci_boot_seq_brkpoint_i,
    output logic         cptra_ss_mcu_no_rom_config_i,
    output logic [31:0]  cptra_ss_strap_mcu_reset_vector_i,
    output logic         cptra_ss_strap_ocp_lock_en_i,
    output logic [15:0]  cptra_ss_strap_key_release_key_size_i,

    input  logic cptra_ss_mcu_halt_status_o,
    output logic cptra_ss_mcu_halt_status_i,
    input  logic cptra_ss_mcu_halt_req_o,
    input  logic cptra_ss_mcu_halt_ack_o,
    output logic cptra_ss_mcu_halt_ack_i,

    axi_if m_axi_bfm_if,

    caliptra_ss_bfm_services_if.bfm tb_services_if

);

localparam KB = 1024;
localparam AXI_AW = $bits(m_axi_bfm_if.araddr);
localparam MCI_REG_SIZE_BYTES               = 2 ** MCI_REG_MIN_ADDR_WIDTH;
localparam MCI_REG_START_ADDR               = `SOC_MCI_TOP_MCI_REG_BASE_ADDR;
localparam MCI_REG_END_ADDR                 = MCI_REG_START_ADDR + (MCI_REG_SIZE_BYTES) - 1;
localparam MCU_TRACE_BUFFER_SIZE_BYTES      = 2 ** TRACE_BUFFER_CSR_MIN_ADDR_WIDTH;
localparam MCU_TRACE_BUFFER_START_ADDR      = `SOC_MCI_TOP_MCU_TRACE_BUFFER_CSR_BASE_ADDR;
localparam MCU_TRACE_BUFFER_END_ADDR        = MCU_TRACE_BUFFER_START_ADDR + (MCU_TRACE_BUFFER_SIZE_BYTES) - 1;
localparam MBOX0_START_ADDR                 = `SOC_MCI_TOP_MCU_MBOX0_CSR_BASE_ADDR;
localparam MBOX0_END_ADDR                   = MBOX0_START_ADDR + ((32'h0000_0001 << MCU_MBOX_CSR_ADDR_WIDTH) - 1);
localparam MBOX1_START_ADDR                 = `SOC_MCI_TOP_MCU_MBOX1_CSR_BASE_ADDR;
localparam MBOX1_END_ADDR                   = MBOX1_START_ADDR + ((32'h0000_0001 << MCU_MBOX_CSR_ADDR_WIDTH) - 1);
localparam MCU_SRAM_START_ADDR              = `SOC_MCI_TOP_MCU_SRAM_BASE_ADDR;
localparam MCU_SRAM_END_ADDR                = MCU_SRAM_START_ADDR + (MCU_SRAM_SIZE_KB * KB) - 1;


// MCU Trace Buffer monitor signals
logic [31:0] mcu_trace_buffer [0:255];
int unsigned mcu_trace_buffer_wr_ptr;
logic mcu_trace_buffer_valid;
logic mcu_trace_buffer_wrapped;
string cptra_ss_test_name;
//flopped signals for assertions
int unsigned trace_buffer_rd_ptr_f;
int unsigned trace_buffer_wr_ptr_f;

// MCU halt/ack control
logic cptra_ss_mcu_halt_status_i_soc_ctrl;
logic cptra_ss_mcu_halt_ack_i_soc_ctrl;

///////////////////////////////////
// TEST FILE INCULDES
//////////////////////////////////
`include "common_test_includes.svh"
`include "mci_test_includes.svh"



initial begin
    ///////////////////////////////////
    // INIT SOC
    //////////////////////////////////
    m_axi_bfm_if.rst_mgr();
    cptra_pwrgood = 1'b0;
    cptra_rst_b = 1'b0;
    tb_services_if.end_test_success = 1'b0;
    tb_services_if.deassert_hard_rst_flag_done = 1'b0;
    tb_services_if.assert_hard_rst_flag_done = 1'b0;
    tb_services_if.deassert_rst_flag_done = 1'b0;
    tb_services_if.assert_rst_flag_done = 1'b0;
    mcu_trace_buffer            = '{default: '0};
    mcu_trace_buffer_wr_ptr     = '0;
    mcu_trace_buffer_valid      = '0;
    mcu_trace_buffer_wrapped    = '0;

    
    
    ///////////////////////////////////
    // Test Sequences
    //////////////////////////////////
    if ($value$plusargs("cptra_ss_sv_test=%s", cptra_ss_test_name)) begin
        $display("[%t] CPTRA SS SV TEST: Test Name from Plusarg: %s", $time, cptra_ss_test_name);
        if (cptra_ss_test_name == "SMOKE_TEST_MCU_SRAM_EXECUTION_REGION") begin
            smoke_test_mcu_sram_execution_region();        
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCU_SRAM_DEBUG_STRESS")begin
            smoke_test_mcu_sram_debug_stress();        
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCU_SRAM_DEBUG_STRESS") begin
            smoke_test_mcu_trace_buffer();
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCU_TRACE_BUFFER") begin
            smoke_test_mcu_trace_buffer();
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCI_AXI_MISS") begin
            smoke_test_mci_axi_miss();
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCU_TRACE_BUFFER_NO_DEBUG") begin
            smoke_test_mcu_trace_buffer_no_debug();
        end
        else if(cptra_ss_test_name == "MCU_MBOX_SOC_AGENT_WRITE_FW_IMAGE") begin
            mcu_mbox_soc_agent_write_fw_image();       
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCI_SOC_CONFIG_DISABLE") begin
            smoke_test_mci_soc_config_disable();       
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCI_SOC_CONFIG_ALWAYS_ENABLE") begin
            smoke_test_mci_soc_config_always_enable();       
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCI_SOC_CONFIG_DIFF_MCU") begin
            smoke_test_mci_soc_config_diff_mcu();       
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCI_BRKPOINT_AXI") begin
            smoke_test_mci_brkpoint_axi();       
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCU_NO_ROM_CONFIG") begin
            smoke_test_mcu_no_rom_config();
        end
        else if(cptra_ss_test_name == "SMOKE_TEST_MCU_NO_ROM_CONFIG_BRKPOINT") begin
            smoke_test_mcu_no_rom_config_brkpoint();
        end
        else begin
            $error("ERROR: Test Name from Plusarg: %s not found", cptra_ss_test_name);
            $finish;
        end
    end
end


///////////////////////////////////
// MCU Halt/Ack control
//////////////////////////////////
initial begin
    cptra_ss_mcu_halt_status_i_soc_ctrl = 1'b0;
    cptra_ss_mcu_halt_ack_i_soc_ctrl = 1'b0;
end 

assign cptra_ss_mcu_halt_status_i = cptra_ss_mcu_halt_status_i_soc_ctrl | cptra_ss_mcu_halt_status_o;
assign cptra_ss_mcu_halt_ack_i    = cptra_ss_mcu_halt_ack_i_soc_ctrl | cptra_ss_mcu_halt_ack_o;

///////////////////////////////////
// MCI Breakpoint              
//////////////////////////////////
initial begin
    
    if ($test$plusargs("MCI_BOOT_FSM_BRKPOINT_SET")) begin
        cptra_ss_mci_boot_seq_brkpoint_i = 1'b1;
        $display("MCI Boot FSM Breakpoint Set");
    end else begin
        cptra_ss_mci_boot_seq_brkpoint_i = 1'b0;
        $display("MCI Boot FSM Breakpoint Not Set");
    end
end

///////////////////////////////////
// MCU NO ROM CONFIG 
//////////////////////////////////
initial begin
    if ($test$plusargs("MCU_NO_ROM_CONFIG_SET")) begin
        cptra_ss_mcu_no_rom_config_i = 1'b1;
        $display("MCU NO ROM CONFIG Set");
    end else begin
        cptra_ss_mcu_no_rom_config_i = 1'b0;
        $display("MCU NO ROM CONFIG Not Set");
    end
end

///////////////////////////////////
// MCU NO ROM CONFIG 
//////////////////////////////////
initial begin
    if ($value$plusargs("MCU_RESET_VECTOR_STRAP_VALUE=%h", cptra_ss_strap_mcu_reset_vector_i)) begin
        $display("MCU Reset Vector Value from Plusarg: %h", cptra_ss_strap_mcu_reset_vector_i);
    end else begin
        cptra_ss_strap_mcu_reset_vector_i    = `css_mcu0_RV_RESET_VEC;
        $display("MCU Reset Vector Value Default to: %h", cptra_ss_strap_mcu_reset_vector_i);
    end
end

///////////////////////////////////
// MONITOR STARTUP             
//////////////////////////////////
initial begin
    fork 
        mcu_trace_buffer_mon();
    join_none
end

///////////////////////////////////
// POWERGOOD REQUEST MONITORING
//////////////////////////////////

always @(posedge core_clk) begin
    if (cycleCnt == 15) begin
        $display("[%t] SOC: INIT Deasserting Hard Reset (cptra_pwrgood)", $time);
        deassert_cptra_pwrgood(5);
    end
    else if (tb_services_if.deassert_hard_rst_flag) begin
        $display("[%t] SOC: Deasserting Hard Reset (cptra_pwrgood)", $time);
        deassert_cptra_pwrgood(100);
        deassert_cptra_rst_b(100);
        tb_services_if.deassert_hard_rst_flag_done <= 1'b1;
    end
    else if ( tb_services_if.assert_hard_rst_flag) begin
        $display("[%t] SOC: Asserting Hard Reset (cptra_pwrgood)", $time);
        halt_mcu_core(100);
        assert_cptra_rst_b(0);
        assert_cptra_pwrgood(0);
        tb_services_if.assert_hard_rst_flag_done <= 1'b1;
    end
    else begin
        tb_services_if.deassert_hard_rst_flag_done <= 1'b0;
        tb_services_if.assert_hard_rst_flag_done <= 1'b0;
    end
end
///////////////////////////////////
// RESET REQUEST MONITORING
//////////////////////////////////
always @(posedge core_clk) begin
    if (cycleCnt == 20) begin
        $display("[%t] SOC: INIT Deasserting Caliptra Reset (cptra_rst_b)", $time);
        deassert_cptra_rst_b(100);
    end
    if (tb_services_if.deassert_rst_flag) begin
        $display("[%t] SOC: Deasserting Caliptra Reset (cptra_rst_b)", $time);
        deassert_cptra_rst_b(100);
        tb_services_if.deassert_rst_flag_done <= 1'b1;
    end
    else if ( tb_services_if.assert_rst_flag) begin
        $display("[%t] SOC: Asserting Caliptra Reset (cptra_rst_b)", $time);
        halt_mcu_core(100);
        assert_cptra_rst_b(100);
        tb_services_if.assert_rst_flag_done <= 1'b1;
    end
    else begin
        tb_services_if.deassert_rst_flag_done <= 1'b0;
        tb_services_if.assert_rst_flag_done <= 1'b0;
    end
end

///////////////////////////////////
// MEK KEY SIZE            
//////////////////////////////////
initial begin
    // Initialize cptra_ss_strap_key_release_key_size_i based on plusargs
    if ($test$plusargs("STRAP_SS_KEY_RELEASE_KEY_SIZE_MANUAL")) begin
        if (!$value$plusargs("STRAP_SS_KEY_RELEASE_KEY_SIZE_MANUAL=%h", cptra_ss_strap_key_release_key_size_i)) begin
            $error("Failed to get value for +STRAP_SS_KEY_RELEASE_KEY_SIZE_MANUAL");
        end
        $display("STRAP_SS_KEY_RELEASE_KEY_SIZE set manually to 0x%04x", cptra_ss_strap_key_release_key_size_i);
    end
    else begin
        // Default value (already DWORD aligned)
        cptra_ss_strap_key_release_key_size_i = 16'h40;
        $display("STRAP_SS_KEY_RELEASE_KEY_SIZE set to default value 0x%04x", cptra_ss_strap_key_release_key_size_i);
    end
end




///////////////////////////////////
// OCP LOCK EN             
//////////////////////////////////
initial begin
    if ($test$plusargs("CLP_OCP_LOCK_EN")) begin
        cptra_ss_strap_ocp_lock_en_i = 1'b1;
    end
    else if ($test$plusargs("CLP_OCP_LOCK_DIS")) begin
        cptra_ss_strap_ocp_lock_en_i = 1'b0;
    end
    else begin
        // Randomize when neither plusarg is set
        cptra_ss_strap_ocp_lock_en_i = $urandom();
    end
end


///////////////////////////////////
// AXI USER VALUES         
//////////////////////////////////
initial begin
    // MCU LSU
    if ($value$plusargs("MCU_LSU_AXI_USER=%h", cptra_ss_strap_mcu_lsu_axi_user_i)) begin
        // Plusarg value is directly assigned to cptra_ss_strap_mcu_lsu_axi_user_i as hex
        $display("MCU LSU AXI USER Value from Plusarg: %h", cptra_ss_strap_mcu_lsu_axi_user_i);
    end else begin
        // Randomize the signal if no plusarg is provided
        cptra_ss_strap_mcu_lsu_axi_user_i = $urandom();
        $display("Randomized MCU LSU AXI USER Value: %h", cptra_ss_strap_mcu_lsu_axi_user_i);
    end
end
initial begin
    // MCU IFU
    if ($value$plusargs("MCU_IFU_AXI_USER=%h", cptra_ss_strap_mcu_ifu_axi_user_i)) begin
        // Plusarg value is directly assigned to cptra_ss_strap_mcu_ifu_axi_user_i as hex
        $display("MCU IFU AXI USER Value from Plusarg: %h", cptra_ss_strap_mcu_ifu_axi_user_i);
    end else begin
        // Randomize the signal if no plusarg is provided
        cptra_ss_strap_mcu_ifu_axi_user_i = $urandom();
        $display("Randomized MCU IFU AXI USER Value: %h", cptra_ss_strap_mcu_ifu_axi_user_i);
    end
end
initial begin
    // Caliptra DMA value
    if ($value$plusargs("CALIPTRA_DMA_AXI_USER=%h", cptra_ss_strap_caliptra_dma_axi_user_i)) begin
        // Plusarg value is directly assigned to cptra_ss_strap_caliptra_dma_axi_user_i as hex
        $display("Caliptra DMA AXI USER Value from Plusarg: %h", cptra_ss_strap_caliptra_dma_axi_user_i);
    end else begin
        // Randomize the signal if no plusarg is provided
        cptra_ss_strap_caliptra_dma_axi_user_i = $urandom();
        $display("Randomized Caliptra DMA AXI USER Value: %h", cptra_ss_strap_caliptra_dma_axi_user_i);
    end
end
initial begin
    // MCU SRAM CONFIG
    if ($value$plusargs("MCU_SRAM_CONFIG_AXI_USER=%h", cptra_ss_strap_mcu_sram_config_axi_user_i)) begin
        // Plusarg value is directly assigned to cptra_ss_strap_mcu_sram_config_axi_user_i as hex
        $display("MCU SRAM CONFIG AXI USER Value from Plusarg: %h", cptra_ss_strap_mcu_sram_config_axi_user_i);
    end else if ($test$plusargs("MCU_SRAM_CONFIG_AXI_USER_RAND")) begin
        // Randomize the signal if no plusarg is provided
        cptra_ss_strap_mcu_sram_config_axi_user_i = $urandom();
        $display("Randomized MCU SRAM CONFIG AXI USER Value: %h", cptra_ss_strap_mcu_sram_config_axi_user_i);
    end else begin
        #1
        cptra_ss_strap_mcu_sram_config_axi_user_i = cptra_ss_strap_caliptra_dma_axi_user_i; 
        $display("MCU SRAM CONFIG AXI USER Value Default to Caliptra DMA: %h", cptra_ss_strap_mcu_sram_config_axi_user_i);
    end
end
initial begin
    // MCU SOC CONFIG
    if ($value$plusargs("MCI_SOC_CONFIG_AXI_USER=%h", cptra_ss_strap_mci_soc_config_axi_user_i)) begin
        // Plusarg value is directly assigned to cptra_ss_strap_mcu_ifu_axi_user_i as hex
        $display("MCI SOC CONFIG AXI USER Value from Plusarg: %h", cptra_ss_strap_mci_soc_config_axi_user_i);
    end else if ($test$plusargs("MCU_SOC_CONFIG_AXI_USER_RAND")) begin
        // Randomize the signal if no plusarg is provided
        cptra_ss_strap_mci_soc_config_axi_user_i= $urandom();
        $display("Randomized MCI SOC CONFIG AXI USER Value: %h", cptra_ss_strap_mci_soc_config_axi_user_i);
    end else begin
        #1
        cptra_ss_strap_mci_soc_config_axi_user_i = cptra_ss_strap_mcu_lsu_axi_user_i; 
        $display("MCI SOC CONFIG AXI USER Value Default to MCU LSU: %h", cptra_ss_strap_mci_soc_config_axi_user_i);
    end
end

endmodule
