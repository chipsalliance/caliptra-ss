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

    axi_if m_axi_bfm_if,

    caliptra_ss_bfm_services_if.bfm tb_services_if
    
    //Interrupt flags
    //input logic assert_hard_rst_flag,
    //input logic assert_rst_flag_from_service,
    //input logic deassert_rst_flag_from_service

);

localparam AXI_AW = $bits(m_axi_bfm_if.araddr);


// MCU Trace Buffer monitor signals
logic [31:0] mcu_trace_buffer [0:255];
int unsigned mcu_trace_buffer_wr_ptr;
logic mcu_trace_buffer_valid;
logic mcu_trace_buffer_wrapped;
string cptra_ss_test_name;

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
        else begin
            $error("ERROR: Test Name from Plusarg: %s not found", cptra_ss_test_name);
            $finish;
        end
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
