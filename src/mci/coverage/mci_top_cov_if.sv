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

`ifndef VERILATOR

interface mci_top_cov_if
    import mci_pkg::*;
    (
    input logic clk,
    // MCI Resets
    input logic mci_rst_b,
    input logic mci_pwrgood,

    // DFT
    input scan_mode,

    // MCI AXI Interface
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,
    
    // Straps
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mcu_lsu_axi_user,
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mcu_ifu_axi_user,
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mcu_sram_config_axi_user,
    input logic [$bits(s_axi_r_if.aruser)-1:0] strap_mci_soc_config_axi_user,
    input logic ss_debug_intent,

    // SRAM ADHOC connections
    input logic mcu_sram_fw_exec_region_lock,

    // SS error signals
    input logic [31:0] agg_error_fatal,
    input logic [31:0] agg_error_non_fatal,

    // SOC Interrupts
    input logic all_error_fatal,
    input logic all_error_non_fatal,
    
    // Generic in/out
    input logic [63:0] mci_generic_input_wires,
    input logic [63:0] mci_generic_output_wires,
    
    // MCU interrupts
    input logic mcu_timer_int,
    input logic mci_intr,

    // MCU Reset vector
    input logic [31:0] strap_mcu_reset_vector, // default reset vector
    input logic [31:0] mcu_reset_vector,       // reset vector used by MCU
    input logic mcu_no_rom_config,                // Determines boot sequencer boot flow

    // NMI Vector 
    input logic nmi_intr,
    input logic [31:0] mcu_nmi_vector,

    // MCU DMI
    input logic        mcu_dmi_core_enable,
    input logic        mcu_dmi_uncore_enable,
    input logic        mcu_dmi_uncore_en,
    input logic        mcu_dmi_uncore_wr_en,
    input logic [ 6:0] mcu_dmi_uncore_addr,
    input logic [31:0] mcu_dmi_uncore_wdata,
    input logic [31:0] mcu_dmi_uncore_rdata,
    input logic        mcu_dmi_active, 

    // MCU Trace
    input logic [31:0] mcu_trace_rv_i_insn_ip,
    input logic [31:0] mcu_trace_rv_i_address_ip,
    input logic        mcu_trace_rv_i_valid_ip,
    input logic        mcu_trace_rv_i_exception_ip,
    input logic [ 4:0] mcu_trace_rv_i_ecause_ip,
    input logic        mcu_trace_rv_i_interrupt_ip,
    input logic [31:0] mcu_trace_rv_i_tval_ip,

    // Caliptra MBOX
    input logic cptra_mbox_data_avail,

    // MBOX
    input logic soc_mcu_mbox0_data_avail,
    input logic soc_mcu_mbox1_data_avail,

    // Reset controls
    input logic mcu_rst_b,
    input logic cptra_rst_b,

    // SoC signals
    input logic mci_boot_seq_brkpoint,

    // LCC Signals
    input logic lc_done,
    input logic lc_init,

    // FC Signals
    input logic fc_opt_done,
    input logic fc_opt_init,

    input logic FIPS_ZEROIZATION_PPD_i,
    input logic FIPS_ZEROIZATION_CMD_o,

    // MCU SRAM Interface
    mci_mcu_sram_if.request mci_mcu_sram_req_if,

    // Mbox0 SRAM Interface
    mci_mcu_sram_if.request mcu_mbox0_sram_req_if,

    // Mbox1 SRAM Interface
    mci_mcu_sram_if.request mcu_mbox1_sram_req_if,


    //=============== LCC GASKET PORTS ========================

    // Inputs from LCC
    input otp_ctrl_pkg::lc_otp_program_req_t            from_lcc_to_otp_program_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_dft_en_i,
    input lc_ctrl_pkg::lc_tx_t                          lc_hw_debug_en_i,
    input                                               lc_fatal_state_error_i,
    // Inputs from OTP_Ctrl
    input  otp_ctrl_pkg::otp_lc_data_t                  from_otp_to_lcc_program_i,
    // Inputs from Caliptra_Core
    input logic                                         ss_dbg_manuf_enable_i,    
    input logic [63:0]                                  ss_soc_dbg_unlock_level_i,

    // Converted Signals from LCC 
    input logic                                         SOC_DFT_EN,
    input logic                                         SOC_HW_DEBUG_EN,

    input soc_ifc_pkg::security_state_t                 security_state_o
);
       

    covergroup mci_top_cg @(posedge clk);
        option.per_instance = 1;

        mci_rst_b_cp: coverpoint mci_rst_b;
        mcu_rst_b_cp: coverpoint  mcu_rst_b;
        cptra_rst_b_cp: coverpoint  cptra_rst_b;
        mci_pwrgood_cp: coverpoint mci_pwrgood;    

        all_error_fatal_cp: coverpoint all_error_fatal;
        all_error_non_fatal_cp: coverpoint all_error_non_fatal;

        mcu_timer_int_cp: coverpoint  mcu_timer_int;
        mci_intr_cp: coverpoint  mci_intr;
        nmi_intr_cp: coverpoint  nmi_intr;
        cptra_mbox_data_avail_cp: coverpoint  cptra_mbox_data_avail;
        soc_mcu_mbox0_data_avail_cp: coverpoint  soc_mcu_mbox0_data_avail;
        soc_mcu_mbox1_data_avail_cp: coverpoint  soc_mcu_mbox1_data_avail;
        mci_boot_seq_brkpoint_cp: coverpoint  mci_boot_seq_brkpoint;
        lc_done_cp: coverpoint  lc_done;
        lc_init_cp: coverpoint  lc_init;
        fc_opt_done_cp: coverpoint  fc_opt_done;
        fc_opt_init_cp: coverpoint  fc_opt_init;
    endgroup

    // Each state in MCI Boot Sequencer
    covergroup mci_boot_seqr_cg @(posedge clk iff mci_rst_b);
        option.per_instance = 1;

        // Each state entered
        boot_states: coverpoint i_boot_seqr.boot_fsm {
            illegal_bins bin_unknown = {BOOT_UNKNOWN};
        }
        // Explicitly cover transitions where boot_fsm could take several branches
        boot_state_transition: coverpoint i_boot_seqr.boot_fsm {
            bins bin_bp_chk_bp = (BOOT_BREAKPOINT_CHECK => BOOT_BREAKPOINT);
            bins bin_bp_chk_cptra = (BOOT_BREAKPOINT_CHECK => BOOT_WAIT_CPTRA_GO);
            bins bin_bp_chk_mcu = (BOOT_BREAKPOINT_CHECK => BOOT_MCU);
            bins bin_bp_cptra = (BOOT_BREAKPOINT => BOOT_WAIT_CPTRA_GO);
            bins bin_bp_mcu = (BOOT_BREAKPOINT => BOOT_MCU);
            bins bin_mcu_rst = (BOOT_MCU => BOOT_WAIT_MCU_RST_REQ);
            bins bin_mcu_cptra = (BOOT_MCU => BOOT_WAIT_CPTRA_GO);
            bins bin_rst_mcu = (BOOT_RST_MCU => BOOT_MCU);
        }
    endgroup

    //Check toggles of generic wires
    covergroup generic_wires_cg(input logic generic_bit) @(posedge clk);
        option.per_instance = 1;
        value:      coverpoint generic_bit;
        transition: coverpoint generic_bit {
            bins bin01 = (0 => 1);
            bins bin10 = (1 => 0);
        }
    endgroup

    mci_top_cg mci_top_cg1 = new();
    mci_boot_seqr_cg mci_boot_seqr_cg1 = new();
    
    generic_wires_cg giw_cg[64];
    generic_wires_cg gow_cg[64];
    generic_wires_cg agg_err_fatal_cg[32];
    generic_wires_cg agg_err_non_fatal_cg[32];
    initial begin
        for(int i = 0; i < 64; i++) begin
            giw_cg[i] = new(mci_generic_input_wires[i]);
            gow_cg[i] = new(mci_generic_output_wires[i]);
        end
        for(int i = 0; i < 32; i++) begin
            agg_err_fatal_cg[i] = new(agg_error_fatal[i]);
            agg_err_non_fatal_cg[i] = new(agg_error_non_fatal[i]);
        end
    end


    covergroup port_lcc_st_trans_toggle_coverage @(posedge clk);
        // Single-bit ports toggle coverage
        coverpoint lc_dft_en_i {
            bins toggled = {1'b0, 1'b1};
        }
        coverpoint lc_hw_debug_en_i {
            bins toggled = {1'b0, 1'b1};
        }
        coverpoint ss_dbg_manuf_enable_i {
            bins toggled = {1'b0, 1'b1};
        }
        coverpoint FIPS_ZEROIZATION_PPD_i {
            bins toggled = {1'b0, 1'b1};
        }
        coverpoint FIPS_ZEROIZATION_CMD_o {
            bins toggled = {1'b0, 1'b1};
        }
        coverpoint SOC_DFT_EN {
            bins toggled = {1'b0, 1'b1};
        }
        coverpoint SOC_HW_DEBUG_EN {
            bins toggled = {1'b0, 1'b1};
        }
    endgroup

    // Coverage for multi-bit ports using toggle_cg
    covergroup multi_bit_toggle_cg with function sample(bit eachbit);
        option.per_instance = 0;
        type_option.merge_instances = 1;
        coverpoint eachbit {
            bins toggle = (0 => 1);
        }
    endgroup

    // Instantiate coverage groups
    multi_bit_toggle_cg prod_unlock_level[64]; // Maximum size for multi-bit ports

    initial begin        
        port_lcc_st_trans_toggle_coverage lcc_st_trans_single_bit_cov = new();
        foreach (prod_unlock_level[ii]) begin
            prod_unlock_level[ii] = new();
        end
    end

endinterface

`endif
