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

    enum bit [1:0] {IDLE = '0, AXI_RD = 2'h2, AXI_WR = 2'h1} bus_event_e;

    // Define read and write detection signals
    logic axi_rd;
    logic axi_wr;

    // Detect read transaction
    assign axi_rd = s_axi_r_if.arvalid && s_axi_r_if.arready;

    // Detect write transaction
    assign axi_wr = s_axi_w_if.awvalid && s_axi_w_if.awready;

    // Address selection logic
    logic [$bits(s_axi_r_if.araddr)-1:0] axi_addr;
    assign axi_addr = axi_rd ? s_axi_r_if.araddr[$bits(s_axi_r_if.araddr)-1:0] : 
                      axi_wr ? s_axi_w_if.awaddr[$bits(s_axi_r_if.araddr)-1:0] :
                      {$bits(s_axi_r_if.araddr){1'b0}};
       

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


  
  
  // ------------------------------------------------------------------- 
  // begin SCRIPT_OUTPUT
  // ------------------------------------------------------------------- 

  // ------------------- COVERGROUP related signals & assigns -------------------

    logic          hit_HW_CAPABILITIES;
    logic [1:0]    bus_HW_CAPABILITIES;
    logic [31:0]   full_addr_HW_CAPABILITIES = `SOC_MCI_TOP_MCI_REG_HW_CAPABILITIES;
  
    logic          hit_FW_CAPABILITIES;
    logic [1:0]    bus_FW_CAPABILITIES;
    logic [31:0]   full_addr_FW_CAPABILITIES = `SOC_MCI_TOP_MCI_REG_FW_CAPABILITIES;
  
    logic          hit_CAP_LOCK;
    logic [1:0]    bus_CAP_LOCK;
    logic [31:0]   full_addr_CAP_LOCK = `SOC_MCI_TOP_MCI_REG_CAP_LOCK;
  
    // logic          hit_HW_REV_ID;
    // logic [1:0]    bus_HW_REV_ID;
    // logic [31:0]   full_addr_HW_REV_ID = `SOC_MCI_TOP_MCI_REG_HW_REV_ID;
  
    logic          hit_FW_REV_ID[0:1];
    logic [1:0]    bus_FW_REV_ID[0:1];
    logic [31:0]   full_addr_FW_REV_ID[0:1];
    assign         full_addr_FW_REV_ID[0] = `SOC_MCI_TOP_MCI_REG_FW_REV_ID_0;
    assign         full_addr_FW_REV_ID[1] = `SOC_MCI_TOP_MCI_REG_FW_REV_ID_1;
  
    // logic          hit_HW_CONFIG0;
    // logic [1:0]    bus_HW_CONFIG0;
    // logic [31:0]   full_addr_HW_CONFIG0 = `SOC_MCI_TOP_MCI_REG_HW_CONFIG0;
  
    // logic          hit_HW_CONFIG1;
    // logic [1:0]    bus_HW_CONFIG1;
    // logic [31:0]   full_addr_HW_CONFIG1 = `SOC_MCI_TOP_MCI_REG_HW_CONFIG1;
  
    logic          hit_FW_FLOW_STATUS;
    logic [1:0]    bus_FW_FLOW_STATUS;
    logic [31:0]   full_addr_FW_FLOW_STATUS = `SOC_MCI_TOP_MCI_REG_FW_FLOW_STATUS;
  
    logic          hit_HW_FLOW_STATUS;
    logic [1:0]    bus_HW_FLOW_STATUS;
    logic [31:0]   full_addr_HW_FLOW_STATUS = `SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS;
  
    logic          hit_RESET_REASON;
    logic [1:0]    bus_RESET_REASON;
    logic [31:0]   full_addr_RESET_REASON = `SOC_MCI_TOP_MCI_REG_RESET_REASON;
  
    logic          hit_RESET_STATUS;
    logic [1:0]    bus_RESET_STATUS;
    logic [31:0]   full_addr_RESET_STATUS = `SOC_MCI_TOP_MCI_REG_RESET_STATUS;
  
    // logic          hit_SECURITY_STATE;
    // logic [1:0]    bus_SECURITY_STATE;
    // logic [31:0]   full_addr_SECURITY_STATE = `SOC_MCI_TOP_MCI_REG_SECURITY_STATE;
  
    logic          hit_HW_ERROR_FATAL;
    logic [1:0]    bus_HW_ERROR_FATAL;
    logic [31:0]   full_addr_HW_ERROR_FATAL = `SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL;
  
    logic          hit_AGG_ERROR_FATAL;
    logic [1:0]    bus_AGG_ERROR_FATAL;
    logic [31:0]   full_addr_AGG_ERROR_FATAL = `SOC_MCI_TOP_MCI_REG_AGG_ERROR_FATAL;
  
    logic          hit_HW_ERROR_NON_FATAL;
    logic [1:0]    bus_HW_ERROR_NON_FATAL;
    logic [31:0]   full_addr_HW_ERROR_NON_FATAL = `SOC_MCI_TOP_MCI_REG_HW_ERROR_NON_FATAL;
  
    logic          hit_AGG_ERROR_NON_FATAL;
    logic [1:0]    bus_AGG_ERROR_NON_FATAL;
    logic [31:0]   full_addr_AGG_ERROR_NON_FATAL = `SOC_MCI_TOP_MCI_REG_AGG_ERROR_NON_FATAL;
  
    logic          hit_FW_ERROR_FATAL;
    logic [1:0]    bus_FW_ERROR_FATAL;
    logic [31:0]   full_addr_FW_ERROR_FATAL = `SOC_MCI_TOP_MCI_REG_FW_ERROR_FATAL;
  
    logic          hit_FW_ERROR_NON_FATAL;
    logic [1:0]    bus_FW_ERROR_NON_FATAL;
    logic [31:0]   full_addr_FW_ERROR_NON_FATAL = `SOC_MCI_TOP_MCI_REG_FW_ERROR_NON_FATAL;
  
    logic          hit_HW_ERROR_ENC;
    logic [1:0]    bus_HW_ERROR_ENC;
    logic [31:0]   full_addr_HW_ERROR_ENC = `SOC_MCI_TOP_MCI_REG_HW_ERROR_ENC;
  
    logic          hit_FW_ERROR_ENC;
    logic [1:0]    bus_FW_ERROR_ENC;
    logic [31:0]   full_addr_FW_ERROR_ENC = `SOC_MCI_TOP_MCI_REG_FW_ERROR_ENC;
  
    logic          hit_FW_EXTENDED_ERROR_INFO[0:7];
    logic [1:0]    bus_FW_EXTENDED_ERROR_INFO[0:7];
    logic [31:0]   full_addr_FW_EXTENDED_ERROR_INFO[0:7];
    assign         full_addr_FW_EXTENDED_ERROR_INFO[0] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_0;
    assign         full_addr_FW_EXTENDED_ERROR_INFO[1] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_1;
    assign         full_addr_FW_EXTENDED_ERROR_INFO[2] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_2;
    assign         full_addr_FW_EXTENDED_ERROR_INFO[3] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_3;
    assign         full_addr_FW_EXTENDED_ERROR_INFO[4] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_4;
    assign         full_addr_FW_EXTENDED_ERROR_INFO[5] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_5;
    assign         full_addr_FW_EXTENDED_ERROR_INFO[6] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_6;
    assign         full_addr_FW_EXTENDED_ERROR_INFO[7] = `SOC_MCI_TOP_MCI_REG_FW_EXTENDED_ERROR_INFO_7;
  
    logic          hit_WDT_TIMER1_EN;
    logic [1:0]    bus_WDT_TIMER1_EN;
    logic [31:0]   full_addr_WDT_TIMER1_EN = `SOC_MCI_TOP_MCI_REG_WDT_TIMER1_EN;
  
    logic          hit_WDT_TIMER1_CTRL;
    logic [1:0]    bus_WDT_TIMER1_CTRL;
    logic [31:0]   full_addr_WDT_TIMER1_CTRL = `SOC_MCI_TOP_MCI_REG_WDT_TIMER1_CTRL;
  
    logic          hit_WDT_TIMER1_TIMEOUT_PERIOD[0:1];
    logic [1:0]    bus_WDT_TIMER1_TIMEOUT_PERIOD[0:1];
    logic [31:0]   full_addr_WDT_TIMER1_TIMEOUT_PERIOD[0:1];
    assign         full_addr_WDT_TIMER1_TIMEOUT_PERIOD[0] = `SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_0;
    assign         full_addr_WDT_TIMER1_TIMEOUT_PERIOD[1] = `SOC_MCI_TOP_MCI_REG_WDT_TIMER1_TIMEOUT_PERIOD_1;
  
    logic          hit_WDT_TIMER2_EN;
    logic [1:0]    bus_WDT_TIMER2_EN;
    logic [31:0]   full_addr_WDT_TIMER2_EN = `SOC_MCI_TOP_MCI_REG_WDT_TIMER2_EN;
  
    logic          hit_WDT_TIMER2_CTRL;
    logic [1:0]    bus_WDT_TIMER2_CTRL;
    logic [31:0]   full_addr_WDT_TIMER2_CTRL = `SOC_MCI_TOP_MCI_REG_WDT_TIMER2_CTRL;
  
    logic          hit_WDT_TIMER2_TIMEOUT_PERIOD[0:1];
    logic [1:0]    bus_WDT_TIMER2_TIMEOUT_PERIOD[0:1];
    logic [31:0]   full_addr_WDT_TIMER2_TIMEOUT_PERIOD[0:1];
    assign         full_addr_WDT_TIMER2_TIMEOUT_PERIOD[0] = `SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_0;
    assign         full_addr_WDT_TIMER2_TIMEOUT_PERIOD[1] = `SOC_MCI_TOP_MCI_REG_WDT_TIMER2_TIMEOUT_PERIOD_1;
  
    logic          hit_WDT_STATUS;
    logic [1:0]    bus_WDT_STATUS;
    logic [31:0]   full_addr_WDT_STATUS = `SOC_MCI_TOP_MCI_REG_WDT_STATUS;
  
    logic          hit_WDT_CFG[0:1];
    logic [1:0]    bus_WDT_CFG[0:1];
    logic [31:0]   full_addr_WDT_CFG[0:1];
    assign         full_addr_WDT_CFG[0] = `SOC_MCI_TOP_MCI_REG_WDT_CFG_0;
    assign         full_addr_WDT_CFG[1] = `SOC_MCI_TOP_MCI_REG_WDT_CFG_1;
  
    logic          hit_MCU_TIMER_CONFIG;
    logic [1:0]    bus_MCU_TIMER_CONFIG;
    logic [31:0]   full_addr_MCU_TIMER_CONFIG = `SOC_MCI_TOP_MCI_REG_MCU_TIMER_CONFIG;
  
    logic          hit_MCU_RV_MTIME_L;
    logic [1:0]    bus_MCU_RV_MTIME_L;
    logic [31:0]   full_addr_MCU_RV_MTIME_L = `SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_L;
  
    logic          hit_MCU_RV_MTIME_H;
    logic [1:0]    bus_MCU_RV_MTIME_H;
    logic [31:0]   full_addr_MCU_RV_MTIME_H = `SOC_MCI_TOP_MCI_REG_MCU_RV_MTIME_H;
  
    logic          hit_MCU_RV_MTIMECMP_L;
    logic [1:0]    bus_MCU_RV_MTIMECMP_L;
    logic [31:0]   full_addr_MCU_RV_MTIMECMP_L = `SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_L;
  
    logic          hit_MCU_RV_MTIMECMP_H;
    logic [1:0]    bus_MCU_RV_MTIMECMP_H;
    logic [31:0]   full_addr_MCU_RV_MTIMECMP_H = `SOC_MCI_TOP_MCI_REG_MCU_RV_MTIMECMP_H;
  
    logic          hit_RESET_REQUEST;
    logic [1:0]    bus_RESET_REQUEST;
    logic [31:0]   full_addr_RESET_REQUEST = `SOC_MCI_TOP_MCI_REG_RESET_REQUEST;
  
    logic          hit_MCI_BOOTFSM_GO;
    logic [1:0]    bus_MCI_BOOTFSM_GO;
    logic [31:0]   full_addr_MCI_BOOTFSM_GO = `SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO;
  
    logic          hit_CPTRA_BOOT_GO;
    logic [1:0]    bus_CPTRA_BOOT_GO;
    logic [31:0]   full_addr_CPTRA_BOOT_GO = `SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO;
  
    logic          hit_FW_SRAM_EXEC_REGION_SIZE;
    logic [1:0]    bus_FW_SRAM_EXEC_REGION_SIZE;
    logic [31:0]   full_addr_FW_SRAM_EXEC_REGION_SIZE = `SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE;
  
    logic          hit_MCU_NMI_VECTOR;
    logic [1:0]    bus_MCU_NMI_VECTOR;
    logic [31:0]   full_addr_MCU_NMI_VECTOR = `SOC_MCI_TOP_MCI_REG_MCU_NMI_VECTOR;
  
    logic          hit_MCU_RESET_VECTOR;
    logic [1:0]    bus_MCU_RESET_VECTOR;
    logic [31:0]   full_addr_MCU_RESET_VECTOR = `SOC_MCI_TOP_MCI_REG_MCU_RESET_VECTOR;
  
    logic          hit_MBOX0_VALID_AXI_USER[0:4];
    logic [1:0]    bus_MBOX0_VALID_AXI_USER[0:4];
    logic [31:0]   full_addr_MBOX0_VALID_AXI_USER[0:4];
    assign         full_addr_MBOX0_VALID_AXI_USER[0] = `SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_0;
    assign         full_addr_MBOX0_VALID_AXI_USER[1] = `SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_1;
    assign         full_addr_MBOX0_VALID_AXI_USER[2] = `SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_2;
    assign         full_addr_MBOX0_VALID_AXI_USER[3] = `SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_3;
    assign         full_addr_MBOX0_VALID_AXI_USER[4] = `SOC_MCI_TOP_MCI_REG_MBOX0_VALID_AXI_USER_4;
  
    logic          hit_MBOX0_AXI_USER_LOCK[0:4];
    logic [1:0]    bus_MBOX0_AXI_USER_LOCK[0:4];
    logic [31:0]   full_addr_MBOX0_AXI_USER_LOCK[0:4];
    assign         full_addr_MBOX0_AXI_USER_LOCK[0] = `SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_0;
    assign         full_addr_MBOX0_AXI_USER_LOCK[1] = `SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_1;
    assign         full_addr_MBOX0_AXI_USER_LOCK[2] = `SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_2;
    assign         full_addr_MBOX0_AXI_USER_LOCK[3] = `SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_3;
    assign         full_addr_MBOX0_AXI_USER_LOCK[4] = `SOC_MCI_TOP_MCI_REG_MBOX0_AXI_USER_LOCK_4;
  
    logic          hit_MBOX1_VALID_AXI_USER[0:4];
    logic [1:0]    bus_MBOX1_VALID_AXI_USER[0:4];
    logic [31:0]   full_addr_MBOX1_VALID_AXI_USER[0:4];
    assign         full_addr_MBOX1_VALID_AXI_USER[0] = `SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_0;
    assign         full_addr_MBOX1_VALID_AXI_USER[1] = `SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_1;
    assign         full_addr_MBOX1_VALID_AXI_USER[2] = `SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_2;
    assign         full_addr_MBOX1_VALID_AXI_USER[3] = `SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_3;
    assign         full_addr_MBOX1_VALID_AXI_USER[4] = `SOC_MCI_TOP_MCI_REG_MBOX1_VALID_AXI_USER_4;
  
    logic          hit_SOC_DFT_EN[0:1];
    logic [1:0]    bus_SOC_DFT_EN[0:1];
    logic [31:0]   full_addr_SOC_DFT_EN[0:1];
    assign         full_addr_SOC_DFT_EN[0] = `SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_0;
    assign         full_addr_SOC_DFT_EN[1] = `SOC_MCI_TOP_MCI_REG_SOC_DFT_EN_1;
  
    logic          hit_SOC_HW_DEBUG_EN[0:1];
    logic [1:0]    bus_SOC_HW_DEBUG_EN[0:1];
    logic [31:0]   full_addr_SOC_HW_DEBUG_EN[0:1];
    assign         full_addr_SOC_HW_DEBUG_EN[0] = `SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_0;
    assign         full_addr_SOC_HW_DEBUG_EN[1] = `SOC_MCI_TOP_MCI_REG_SOC_HW_DEBUG_EN_1;
  
    logic          hit_SOC_PROD_DEBUG_STATE[0:1];
    logic [1:0]    bus_SOC_PROD_DEBUG_STATE[0:1];
    logic [31:0]   full_addr_SOC_PROD_DEBUG_STATE[0:1];
    assign         full_addr_SOC_PROD_DEBUG_STATE[0] = `SOC_MCI_TOP_MCI_REG_SOC_PROD_DEBUG_STATE_0;
    assign         full_addr_SOC_PROD_DEBUG_STATE[1] = `SOC_MCI_TOP_MCI_REG_SOC_PROD_DEBUG_STATE_1;
  
    logic          hit_FC_FIPS_ZEROZATION;
    logic [1:0]    bus_FC_FIPS_ZEROZATION;
    logic [31:0]   full_addr_FC_FIPS_ZEROZATION = `SOC_MCI_TOP_MCI_REG_FC_FIPS_ZEROZATION;
  
    logic          hit_GENERIC_INPUT_WIRES[0:1];
    logic [1:0]    bus_GENERIC_INPUT_WIRES[0:1];
    logic [31:0]   full_addr_GENERIC_INPUT_WIRES[0:1];
    assign         full_addr_GENERIC_INPUT_WIRES[0] = `SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_0;
    assign         full_addr_GENERIC_INPUT_WIRES[1] = `SOC_MCI_TOP_MCI_REG_GENERIC_INPUT_WIRES_1;
  
    logic          hit_GENERIC_OUTPUT_WIRES[0:1];
    logic [1:0]    bus_GENERIC_OUTPUT_WIRES[0:1];
    logic [31:0]   full_addr_GENERIC_OUTPUT_WIRES[0:1];
    assign         full_addr_GENERIC_OUTPUT_WIRES[0] = `SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_0;
    assign         full_addr_GENERIC_OUTPUT_WIRES[1] = `SOC_MCI_TOP_MCI_REG_GENERIC_OUTPUT_WIRES_1;
  
    logic          hit_DEBUG_IN;
    logic [1:0]    bus_DEBUG_IN;
    logic [31:0]   full_addr_DEBUG_IN = `SOC_MCI_TOP_MCI_REG_DEBUG_IN;
  
    logic          hit_DEBUG_OUT;
    logic [1:0]    bus_DEBUG_OUT;
    logic [31:0]   full_addr_DEBUG_OUT = `SOC_MCI_TOP_MCI_REG_DEBUG_OUT;
  
    logic          hit_SS_DEBUG_INTENT;
    logic [1:0]    bus_SS_DEBUG_INTENT;
    logic [31:0]   full_addr_SS_DEBUG_INTENT = `SOC_MCI_TOP_MCI_REG_SS_DEBUG_INTENT;
  
    logic          hit_SS_CONFIG_DONE_STICKY;
    logic [1:0]    bus_SS_CONFIG_DONE_STICKY;
    logic [31:0]   full_addr_SS_CONFIG_DONE_STICKY = `SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE_STICKY;
  
    logic          hit_SS_CONFIG_DONE;
    logic [1:0]    bus_SS_CONFIG_DONE;
    logic [31:0]   full_addr_SS_CONFIG_DONE = `SOC_MCI_TOP_MCI_REG_SS_CONFIG_DONE;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_11;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_11;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_11;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_11;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_11;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_11;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_11;
  
    logic          hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0:11];
    logic [1:0]    bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0:11];
    logic [31:0]   full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0:11];
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_0;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[1] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_1;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[2] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_2;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[3] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_3;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[4] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_4;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[5] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_5;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[6] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_6;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[7] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_7;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[8] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_8;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[9] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_9;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[10] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_10;
    assign         full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[11] = `SOC_MCI_TOP_MCI_REG_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_11;
  
    logic          hit_INTR_BLOCK_RF_GLOBAL_INTR_EN_R;
    logic [1:0]    bus_INTR_BLOCK_RF_GLOBAL_INTR_EN_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_GLOBAL_INTR_EN_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR0_INTR_EN_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR0_INTR_EN_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR0_INTR_EN_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_EN_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR1_INTR_EN_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR1_INTR_EN_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR1_INTR_EN_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_EN_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF0_INTR_EN_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF0_INTR_EN_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF0_INTR_EN_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_EN_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF1_INTR_EN_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF1_INTR_EN_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF1_INTR_EN_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_EN_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R;
  
    logic          hit_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R;
    logic [1:0]    bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R;
    logic [31:0]   full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R = `SOC_MCI_TOP_MCI_REG_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R;
  
  
    assign hit_HW_CAPABILITIES = (axi_addr == full_addr_HW_CAPABILITIES[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_HW_CAPABILITIES = {axi_rd, axi_wr} & {2{hit_HW_CAPABILITIES}};
  
    assign hit_FW_CAPABILITIES = (axi_addr == full_addr_FW_CAPABILITIES[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_CAPABILITIES = {axi_rd, axi_wr} & {2{hit_FW_CAPABILITIES}};
  
    assign hit_CAP_LOCK = (axi_addr == full_addr_CAP_LOCK[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_CAP_LOCK = {axi_rd, axi_wr} & {2{hit_CAP_LOCK}};
  
    // assign hit_HW_REV_ID = (axi_addr == full_addr_HW_REV_ID[$bits(s_axi_r_if.araddr)-1:0]);
    // assign bus_HW_REV_ID = {axi_rd, axi_wr} & {2{hit_HW_REV_ID}};
  
    assign hit_FW_REV_ID[0] = (axi_addr == full_addr_FW_REV_ID[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_REV_ID[0] = {axi_rd, axi_wr} & {2{hit_FW_REV_ID[0]}};
  
    assign hit_FW_REV_ID[1] = (axi_addr == full_addr_FW_REV_ID[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_REV_ID[1] = {axi_rd, axi_wr} & {2{hit_FW_REV_ID[1]}};
  
    // assign hit_HW_CONFIG0 = (axi_addr == full_addr_HW_CONFIG0[$bits(s_axi_r_if.araddr)-1:0]);
    // assign bus_HW_CONFIG0 = {axi_rd, axi_wr} & {2{hit_HW_CONFIG0}};
  
    // assign hit_HW_CONFIG1 = (axi_addr == full_addr_HW_CONFIG1[$bits(s_axi_r_if.araddr)-1:0]);
    // assign bus_HW_CONFIG1 = {axi_rd, axi_wr} & {2{hit_HW_CONFIG1}};
  
    assign hit_FW_FLOW_STATUS = (axi_addr == full_addr_FW_FLOW_STATUS[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_FLOW_STATUS = {axi_rd, axi_wr} & {2{hit_FW_FLOW_STATUS}};
  
    assign hit_HW_FLOW_STATUS = (axi_addr == full_addr_HW_FLOW_STATUS[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_HW_FLOW_STATUS = {axi_rd, axi_wr} & {2{hit_HW_FLOW_STATUS}};
  
    assign hit_RESET_REASON = (axi_addr == full_addr_RESET_REASON[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_RESET_REASON = {axi_rd, axi_wr} & {2{hit_RESET_REASON}};
  
    assign hit_RESET_STATUS = (axi_addr == full_addr_RESET_STATUS[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_RESET_STATUS = {axi_rd, axi_wr} & {2{hit_RESET_STATUS}};
  
    // assign hit_SECURITY_STATE = (axi_addr == full_addr_SECURITY_STATE[$bits(s_axi_r_if.araddr)-1:0]);
    // assign bus_SECURITY_STATE = {axi_rd, axi_wr} & {2{hit_SECURITY_STATE}};
  
    assign hit_HW_ERROR_FATAL = (axi_addr == full_addr_HW_ERROR_FATAL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_HW_ERROR_FATAL = {axi_rd, axi_wr} & {2{hit_HW_ERROR_FATAL}};
  
    assign hit_AGG_ERROR_FATAL = (axi_addr == full_addr_AGG_ERROR_FATAL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_AGG_ERROR_FATAL = {axi_rd, axi_wr} & {2{hit_AGG_ERROR_FATAL}};
  
    assign hit_HW_ERROR_NON_FATAL = (axi_addr == full_addr_HW_ERROR_NON_FATAL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_HW_ERROR_NON_FATAL = {axi_rd, axi_wr} & {2{hit_HW_ERROR_NON_FATAL}};
  
    assign hit_AGG_ERROR_NON_FATAL = (axi_addr == full_addr_AGG_ERROR_NON_FATAL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_AGG_ERROR_NON_FATAL = {axi_rd, axi_wr} & {2{hit_AGG_ERROR_NON_FATAL}};
  
    assign hit_FW_ERROR_FATAL = (axi_addr == full_addr_FW_ERROR_FATAL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_ERROR_FATAL = {axi_rd, axi_wr} & {2{hit_FW_ERROR_FATAL}};
  
    assign hit_FW_ERROR_NON_FATAL = (axi_addr == full_addr_FW_ERROR_NON_FATAL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_ERROR_NON_FATAL = {axi_rd, axi_wr} & {2{hit_FW_ERROR_NON_FATAL}};
  
    assign hit_HW_ERROR_ENC = (axi_addr == full_addr_HW_ERROR_ENC[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_HW_ERROR_ENC = {axi_rd, axi_wr} & {2{hit_HW_ERROR_ENC}};
  
    assign hit_FW_ERROR_ENC = (axi_addr == full_addr_FW_ERROR_ENC[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_ERROR_ENC = {axi_rd, axi_wr} & {2{hit_FW_ERROR_ENC}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[0] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[0] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[0]}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[1] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[1] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[1]}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[2] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[2] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[2]}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[3] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[3] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[3]}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[4] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[4] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[4]}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[5] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[5] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[5]}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[6] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[6] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[6]}};
  
    assign hit_FW_EXTENDED_ERROR_INFO[7] = (axi_addr == full_addr_FW_EXTENDED_ERROR_INFO[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_EXTENDED_ERROR_INFO[7] = {axi_rd, axi_wr} & {2{hit_FW_EXTENDED_ERROR_INFO[7]}};
  
    assign hit_WDT_TIMER1_EN = (axi_addr == full_addr_WDT_TIMER1_EN[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER1_EN = {axi_rd, axi_wr} & {2{hit_WDT_TIMER1_EN}};
  
    assign hit_WDT_TIMER1_CTRL = (axi_addr == full_addr_WDT_TIMER1_CTRL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER1_CTRL = {axi_rd, axi_wr} & {2{hit_WDT_TIMER1_CTRL}};
  
    assign hit_WDT_TIMER1_TIMEOUT_PERIOD[0] = (axi_addr == full_addr_WDT_TIMER1_TIMEOUT_PERIOD[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER1_TIMEOUT_PERIOD[0] = {axi_rd, axi_wr} & {2{hit_WDT_TIMER1_TIMEOUT_PERIOD[0]}};
  
    assign hit_WDT_TIMER1_TIMEOUT_PERIOD[1] = (axi_addr == full_addr_WDT_TIMER1_TIMEOUT_PERIOD[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER1_TIMEOUT_PERIOD[1] = {axi_rd, axi_wr} & {2{hit_WDT_TIMER1_TIMEOUT_PERIOD[1]}};
  
    assign hit_WDT_TIMER2_EN = (axi_addr == full_addr_WDT_TIMER2_EN[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER2_EN = {axi_rd, axi_wr} & {2{hit_WDT_TIMER2_EN}};
  
    assign hit_WDT_TIMER2_CTRL = (axi_addr == full_addr_WDT_TIMER2_CTRL[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER2_CTRL = {axi_rd, axi_wr} & {2{hit_WDT_TIMER2_CTRL}};
  
    assign hit_WDT_TIMER2_TIMEOUT_PERIOD[0] = (axi_addr == full_addr_WDT_TIMER2_TIMEOUT_PERIOD[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER2_TIMEOUT_PERIOD[0] = {axi_rd, axi_wr} & {2{hit_WDT_TIMER2_TIMEOUT_PERIOD[0]}};
  
    assign hit_WDT_TIMER2_TIMEOUT_PERIOD[1] = (axi_addr == full_addr_WDT_TIMER2_TIMEOUT_PERIOD[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_TIMER2_TIMEOUT_PERIOD[1] = {axi_rd, axi_wr} & {2{hit_WDT_TIMER2_TIMEOUT_PERIOD[1]}};
  
    assign hit_WDT_STATUS = (axi_addr == full_addr_WDT_STATUS[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_STATUS = {axi_rd, axi_wr} & {2{hit_WDT_STATUS}};
  
    assign hit_WDT_CFG[0] = (axi_addr == full_addr_WDT_CFG[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_CFG[0] = {axi_rd, axi_wr} & {2{hit_WDT_CFG[0]}};
  
    assign hit_WDT_CFG[1] = (axi_addr == full_addr_WDT_CFG[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_WDT_CFG[1] = {axi_rd, axi_wr} & {2{hit_WDT_CFG[1]}};
  
    assign hit_MCU_TIMER_CONFIG = (axi_addr == full_addr_MCU_TIMER_CONFIG[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCU_TIMER_CONFIG = {axi_rd, axi_wr} & {2{hit_MCU_TIMER_CONFIG}};
  
    assign hit_MCU_RV_MTIME_L = (axi_addr == full_addr_MCU_RV_MTIME_L[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCU_RV_MTIME_L = {axi_rd, axi_wr} & {2{hit_MCU_RV_MTIME_L}};
  
    assign hit_MCU_RV_MTIME_H = (axi_addr == full_addr_MCU_RV_MTIME_H[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCU_RV_MTIME_H = {axi_rd, axi_wr} & {2{hit_MCU_RV_MTIME_H}};
  
    assign hit_MCU_RV_MTIMECMP_L = (axi_addr == full_addr_MCU_RV_MTIMECMP_L[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCU_RV_MTIMECMP_L = {axi_rd, axi_wr} & {2{hit_MCU_RV_MTIMECMP_L}};
  
    assign hit_MCU_RV_MTIMECMP_H = (axi_addr == full_addr_MCU_RV_MTIMECMP_H[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCU_RV_MTIMECMP_H = {axi_rd, axi_wr} & {2{hit_MCU_RV_MTIMECMP_H}};
  
    assign hit_RESET_REQUEST = (axi_addr == full_addr_RESET_REQUEST[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_RESET_REQUEST = {axi_rd, axi_wr} & {2{hit_RESET_REQUEST}};
  
    assign hit_MCI_BOOTFSM_GO = (axi_addr == full_addr_MCI_BOOTFSM_GO[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCI_BOOTFSM_GO = {axi_rd, axi_wr} & {2{hit_MCI_BOOTFSM_GO}};
  
    assign hit_CPTRA_BOOT_GO = (axi_addr == full_addr_CPTRA_BOOT_GO[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_CPTRA_BOOT_GO = {axi_rd, axi_wr} & {2{hit_CPTRA_BOOT_GO}};
  
    assign hit_FW_SRAM_EXEC_REGION_SIZE = (axi_addr == full_addr_FW_SRAM_EXEC_REGION_SIZE[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FW_SRAM_EXEC_REGION_SIZE = {axi_rd, axi_wr} & {2{hit_FW_SRAM_EXEC_REGION_SIZE}};
  
    assign hit_MCU_NMI_VECTOR = (axi_addr == full_addr_MCU_NMI_VECTOR[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCU_NMI_VECTOR = {axi_rd, axi_wr} & {2{hit_MCU_NMI_VECTOR}};
  
    assign hit_MCU_RESET_VECTOR = (axi_addr == full_addr_MCU_RESET_VECTOR[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MCU_RESET_VECTOR = {axi_rd, axi_wr} & {2{hit_MCU_RESET_VECTOR}};
  
    assign hit_MBOX0_VALID_AXI_USER[0] = (axi_addr == full_addr_MBOX0_VALID_AXI_USER[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_VALID_AXI_USER[0] = {axi_rd, axi_wr} & {2{hit_MBOX0_VALID_AXI_USER[0]}};
  
    assign hit_MBOX0_VALID_AXI_USER[1] = (axi_addr == full_addr_MBOX0_VALID_AXI_USER[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_VALID_AXI_USER[1] = {axi_rd, axi_wr} & {2{hit_MBOX0_VALID_AXI_USER[1]}};
  
    assign hit_MBOX0_VALID_AXI_USER[2] = (axi_addr == full_addr_MBOX0_VALID_AXI_USER[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_VALID_AXI_USER[2] = {axi_rd, axi_wr} & {2{hit_MBOX0_VALID_AXI_USER[2]}};
  
    assign hit_MBOX0_VALID_AXI_USER[3] = (axi_addr == full_addr_MBOX0_VALID_AXI_USER[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_VALID_AXI_USER[3] = {axi_rd, axi_wr} & {2{hit_MBOX0_VALID_AXI_USER[3]}};
  
    assign hit_MBOX0_VALID_AXI_USER[4] = (axi_addr == full_addr_MBOX0_VALID_AXI_USER[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_VALID_AXI_USER[4] = {axi_rd, axi_wr} & {2{hit_MBOX0_VALID_AXI_USER[4]}};
  
    assign hit_MBOX0_AXI_USER_LOCK[0] = (axi_addr == full_addr_MBOX0_AXI_USER_LOCK[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_AXI_USER_LOCK[0] = {axi_rd, axi_wr} & {2{hit_MBOX0_AXI_USER_LOCK[0]}};
  
    assign hit_MBOX0_AXI_USER_LOCK[1] = (axi_addr == full_addr_MBOX0_AXI_USER_LOCK[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_AXI_USER_LOCK[1] = {axi_rd, axi_wr} & {2{hit_MBOX0_AXI_USER_LOCK[1]}};
  
    assign hit_MBOX0_AXI_USER_LOCK[2] = (axi_addr == full_addr_MBOX0_AXI_USER_LOCK[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_AXI_USER_LOCK[2] = {axi_rd, axi_wr} & {2{hit_MBOX0_AXI_USER_LOCK[2]}};
  
    assign hit_MBOX0_AXI_USER_LOCK[3] = (axi_addr == full_addr_MBOX0_AXI_USER_LOCK[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_AXI_USER_LOCK[3] = {axi_rd, axi_wr} & {2{hit_MBOX0_AXI_USER_LOCK[3]}};
  
    assign hit_MBOX0_AXI_USER_LOCK[4] = (axi_addr == full_addr_MBOX0_AXI_USER_LOCK[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX0_AXI_USER_LOCK[4] = {axi_rd, axi_wr} & {2{hit_MBOX0_AXI_USER_LOCK[4]}};
  
    assign hit_MBOX1_VALID_AXI_USER[0] = (axi_addr == full_addr_MBOX1_VALID_AXI_USER[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX1_VALID_AXI_USER[0] = {axi_rd, axi_wr} & {2{hit_MBOX1_VALID_AXI_USER[0]}};
  
    assign hit_MBOX1_VALID_AXI_USER[1] = (axi_addr == full_addr_MBOX1_VALID_AXI_USER[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX1_VALID_AXI_USER[1] = {axi_rd, axi_wr} & {2{hit_MBOX1_VALID_AXI_USER[1]}};
  
    assign hit_MBOX1_VALID_AXI_USER[2] = (axi_addr == full_addr_MBOX1_VALID_AXI_USER[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX1_VALID_AXI_USER[2] = {axi_rd, axi_wr} & {2{hit_MBOX1_VALID_AXI_USER[2]}};
  
    assign hit_MBOX1_VALID_AXI_USER[3] = (axi_addr == full_addr_MBOX1_VALID_AXI_USER[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX1_VALID_AXI_USER[3] = {axi_rd, axi_wr} & {2{hit_MBOX1_VALID_AXI_USER[3]}};
  
    assign hit_MBOX1_VALID_AXI_USER[4] = (axi_addr == full_addr_MBOX1_VALID_AXI_USER[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_MBOX1_VALID_AXI_USER[4] = {axi_rd, axi_wr} & {2{hit_MBOX1_VALID_AXI_USER[4]}};
  
    assign hit_SOC_DFT_EN[0] = (axi_addr == full_addr_SOC_DFT_EN[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SOC_DFT_EN[0] = {axi_rd, axi_wr} & {2{hit_SOC_DFT_EN[0]}};
  
    assign hit_SOC_DFT_EN[1] = (axi_addr == full_addr_SOC_DFT_EN[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SOC_DFT_EN[1] = {axi_rd, axi_wr} & {2{hit_SOC_DFT_EN[1]}};
  
    assign hit_SOC_HW_DEBUG_EN[0] = (axi_addr == full_addr_SOC_HW_DEBUG_EN[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SOC_HW_DEBUG_EN[0] = {axi_rd, axi_wr} & {2{hit_SOC_HW_DEBUG_EN[0]}};
  
    assign hit_SOC_HW_DEBUG_EN[1] = (axi_addr == full_addr_SOC_HW_DEBUG_EN[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SOC_HW_DEBUG_EN[1] = {axi_rd, axi_wr} & {2{hit_SOC_HW_DEBUG_EN[1]}};
  
    assign hit_SOC_PROD_DEBUG_STATE[0] = (axi_addr == full_addr_SOC_PROD_DEBUG_STATE[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SOC_PROD_DEBUG_STATE[0] = {axi_rd, axi_wr} & {2{hit_SOC_PROD_DEBUG_STATE[0]}};
  
    assign hit_SOC_PROD_DEBUG_STATE[1] = (axi_addr == full_addr_SOC_PROD_DEBUG_STATE[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SOC_PROD_DEBUG_STATE[1] = {axi_rd, axi_wr} & {2{hit_SOC_PROD_DEBUG_STATE[1]}};
  
    assign hit_FC_FIPS_ZEROZATION = (axi_addr == full_addr_FC_FIPS_ZEROZATION[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_FC_FIPS_ZEROZATION = {axi_rd, axi_wr} & {2{hit_FC_FIPS_ZEROZATION}};
  
    assign hit_GENERIC_INPUT_WIRES[0] = (axi_addr == full_addr_GENERIC_INPUT_WIRES[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_GENERIC_INPUT_WIRES[0] = {axi_rd, axi_wr} & {2{hit_GENERIC_INPUT_WIRES[0]}};
  
    assign hit_GENERIC_INPUT_WIRES[1] = (axi_addr == full_addr_GENERIC_INPUT_WIRES[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_GENERIC_INPUT_WIRES[1] = {axi_rd, axi_wr} & {2{hit_GENERIC_INPUT_WIRES[1]}};
  
    assign hit_GENERIC_OUTPUT_WIRES[0] = (axi_addr == full_addr_GENERIC_OUTPUT_WIRES[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_GENERIC_OUTPUT_WIRES[0] = {axi_rd, axi_wr} & {2{hit_GENERIC_OUTPUT_WIRES[0]}};
  
    assign hit_GENERIC_OUTPUT_WIRES[1] = (axi_addr == full_addr_GENERIC_OUTPUT_WIRES[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_GENERIC_OUTPUT_WIRES[1] = {axi_rd, axi_wr} & {2{hit_GENERIC_OUTPUT_WIRES[1]}};
  
    assign hit_DEBUG_IN = (axi_addr == full_addr_DEBUG_IN[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_DEBUG_IN = {axi_rd, axi_wr} & {2{hit_DEBUG_IN}};
  
    assign hit_DEBUG_OUT = (axi_addr == full_addr_DEBUG_OUT[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_DEBUG_OUT = {axi_rd, axi_wr} & {2{hit_DEBUG_OUT}};
  
    assign hit_SS_DEBUG_INTENT = (axi_addr == full_addr_SS_DEBUG_INTENT[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SS_DEBUG_INTENT = {axi_rd, axi_wr} & {2{hit_SS_DEBUG_INTENT}};
  
    assign hit_SS_CONFIG_DONE_STICKY = (axi_addr == full_addr_SS_CONFIG_DONE_STICKY[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SS_CONFIG_DONE_STICKY = {axi_rd, axi_wr} & {2{hit_SS_CONFIG_DONE_STICKY}};
  
    assign hit_SS_CONFIG_DONE = (axi_addr == full_addr_SS_CONFIG_DONE[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_SS_CONFIG_DONE = {axi_rd, axi_wr} & {2{hit_SS_CONFIG_DONE}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_0[11]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_1[11]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_2[11]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_3[11]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_4[11]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_5[11]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_6[11]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[0]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[1] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[1][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[1] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[1]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[2] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[2][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[2] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[2]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[3] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[3][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[3] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[3]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[4] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[4][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[4] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[4]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[5] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[5][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[5] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[5]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[6] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[6][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[6] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[6]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[7] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[7][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[7] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[7]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[8] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[8][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[8] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[8]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[9] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[9][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[9] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[9]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[10] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[10][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[10] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[10]}};
  
    assign hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[11] = (axi_addr == full_addr_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[11][$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[11] = {axi_rd, axi_wr} & {2{hit_PROD_DEBUG_UNLOCK_PK_HASH_REG_7[11]}};
  
    assign hit_INTR_BLOCK_RF_GLOBAL_INTR_EN_R = (axi_addr == full_addr_INTR_BLOCK_RF_GLOBAL_INTR_EN_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_GLOBAL_INTR_EN_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_GLOBAL_INTR_EN_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR0_INTR_EN_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR0_INTR_EN_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR0_INTR_EN_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR0_INTR_EN_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR1_INTR_EN_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR1_INTR_EN_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR1_INTR_EN_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR1_INTR_EN_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF0_INTR_EN_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF0_INTR_EN_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF0_INTR_EN_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF0_INTR_EN_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF1_INTR_EN_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF1_INTR_EN_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF1_INTR_EN_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF1_INTR_EN_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R}};
  
    assign hit_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R = (axi_addr == full_addr_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R[$bits(s_axi_r_if.araddr)-1:0]);
    assign bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R = {axi_rd, axi_wr} & {2{hit_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R}};
  
    // ----------------------- COVERGROUP HW_CAPABILITIES -----------------------
    covergroup mci_HW_CAPABILITIES_cg (ref logic [1:0] bus_event) @(posedge clk);
      HW_CAPABILITIES_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_CAPABILITIES;
      bus_HW_CAPABILITIES_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP FW_CAPABILITIES -----------------------
    covergroup mci_FW_CAPABILITIES_cg (ref logic [1:0] bus_event) @(posedge clk);
      FW_CAPABILITIES_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_CAPABILITIES;
      bus_FW_CAPABILITIES_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP CAP_LOCK -----------------------
    covergroup mci_CAP_LOCK_cg (ref logic [1:0] bus_event) @(posedge clk);
      CAP_LOCK_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.CAP_LOCK;
      bus_CAP_LOCK_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // // ----------------------- COVERGROUP HW_REV_ID -----------------------
    // covergroup mci_HW_REV_ID_cg (ref logic [1:0] bus_event) @(posedge clk);
    //   HW_REV_ID_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_REV_ID;
    //   bus_HW_REV_ID_cp : coverpoint bus_event {
    //     bins rd = {AXI_RD};
    //     bins wr = {AXI_WR};
    //     ignore_bins dont_care = {IDLE, 2'h3};
    //   }
    // endgroup
  
    // ----------------------- COVERGROUP FW_REV_ID [0:1] -----------------------
    covergroup mci_FW_REV_ID_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      FW_REV_ID0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_REV_ID[0];
      bus_FW_REV_ID0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_REV_ID1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_REV_ID[1];
      bus_FW_REV_ID1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // // ----------------------- COVERGROUP HW_CONFIG0 -----------------------
    // covergroup mci_HW_CONFIG0_cg (ref logic [1:0] bus_event) @(posedge clk);
    //   HW_CONFIG0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_CONFIG0;
    //   bus_HW_CONFIG0_cp : coverpoint bus_event {
    //     bins rd = {AXI_RD};
    //     bins wr = {AXI_WR};
    //     ignore_bins dont_care = {IDLE, 2'h3};
    //   }
    // endgroup
  
    // // ----------------------- COVERGROUP HW_CONFIG1 -----------------------
    // covergroup mci_HW_CONFIG1_cg (ref logic [1:0] bus_event) @(posedge clk);
    //   HW_CONFIG1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_CONFIG1;
    //   bus_HW_CONFIG1_cp : coverpoint bus_event {
    //     bins rd = {AXI_RD};
    //     bins wr = {AXI_WR};
    //     ignore_bins dont_care = {IDLE, 2'h3};
    //   }
    // endgroup
  
    // ----------------------- COVERGROUP FW_FLOW_STATUS -----------------------
    covergroup mci_FW_FLOW_STATUS_cg (ref logic [1:0] bus_event) @(posedge clk);
      FW_FLOW_STATUS_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_FLOW_STATUS;
      bus_FW_FLOW_STATUS_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP HW_FLOW_STATUS -----------------------
    covergroup mci_HW_FLOW_STATUS_cg (ref logic [1:0] bus_event) @(posedge clk);
      HW_FLOW_STATUS_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_FLOW_STATUS;
      bus_HW_FLOW_STATUS_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP RESET_REASON -----------------------
    covergroup mci_RESET_REASON_cg (ref logic [1:0] bus_event) @(posedge clk);
      RESET_REASON_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.RESET_REASON;
      bus_RESET_REASON_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP RESET_STATUS -----------------------
    covergroup mci_RESET_STATUS_cg (ref logic [1:0] bus_event) @(posedge clk);
      RESET_STATUS_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.RESET_STATUS;
      bus_RESET_STATUS_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // // ----------------------- COVERGROUP SECURITY_STATE -----------------------
    // covergroup mci_SECURITY_STATE_cg (ref logic [1:0] bus_event) @(posedge clk);
    //   SECURITY_STATE_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SECURITY_STATE;
    //   bus_SECURITY_STATE_cp : coverpoint bus_event {
    //     bins rd = {AXI_RD};
    //     bins wr = {AXI_WR};
    //     ignore_bins dont_care = {IDLE, 2'h3};
    //   }
    // endgroup
  
    // ----------------------- COVERGROUP HW_ERROR_FATAL -----------------------
    covergroup mci_HW_ERROR_FATAL_cg (ref logic [1:0] bus_event) @(posedge clk);
      HW_ERROR_FATAL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_ERROR_FATAL;
      bus_HW_ERROR_FATAL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP AGG_ERROR_FATAL -----------------------
    covergroup mci_AGG_ERROR_FATAL_cg (ref logic [1:0] bus_event) @(posedge clk);
      AGG_ERROR_FATAL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.AGG_ERROR_FATAL;
      bus_AGG_ERROR_FATAL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP HW_ERROR_NON_FATAL -----------------------
    covergroup mci_HW_ERROR_NON_FATAL_cg (ref logic [1:0] bus_event) @(posedge clk);
      HW_ERROR_NON_FATAL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_ERROR_NON_FATAL;
      bus_HW_ERROR_NON_FATAL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP AGG_ERROR_NON_FATAL -----------------------
    covergroup mci_AGG_ERROR_NON_FATAL_cg (ref logic [1:0] bus_event) @(posedge clk);
      AGG_ERROR_NON_FATAL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.AGG_ERROR_NON_FATAL;
      bus_AGG_ERROR_NON_FATAL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP FW_ERROR_FATAL -----------------------
    covergroup mci_FW_ERROR_FATAL_cg (ref logic [1:0] bus_event) @(posedge clk);
      FW_ERROR_FATAL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_ERROR_FATAL;
      bus_FW_ERROR_FATAL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP FW_ERROR_NON_FATAL -----------------------
    covergroup mci_FW_ERROR_NON_FATAL_cg (ref logic [1:0] bus_event) @(posedge clk);
      FW_ERROR_NON_FATAL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_ERROR_NON_FATAL;
      bus_FW_ERROR_NON_FATAL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP HW_ERROR_ENC -----------------------
    covergroup mci_HW_ERROR_ENC_cg (ref logic [1:0] bus_event) @(posedge clk);
      HW_ERROR_ENC_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.HW_ERROR_ENC;
      bus_HW_ERROR_ENC_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP FW_ERROR_ENC -----------------------
    covergroup mci_FW_ERROR_ENC_cg (ref logic [1:0] bus_event) @(posedge clk);
      FW_ERROR_ENC_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_ERROR_ENC;
      bus_FW_ERROR_ENC_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP FW_EXTENDED_ERROR_INFO [0:7] -----------------------
    covergroup mci_FW_EXTENDED_ERROR_INFO_cg (ref logic [1:0] bus_event[0:7]) @(posedge clk);
      FW_EXTENDED_ERROR_INFO0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[0];
      bus_FW_EXTENDED_ERROR_INFO0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_EXTENDED_ERROR_INFO1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[1];
      bus_FW_EXTENDED_ERROR_INFO1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_EXTENDED_ERROR_INFO2_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[2];
      bus_FW_EXTENDED_ERROR_INFO2_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_EXTENDED_ERROR_INFO3_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[3];
      bus_FW_EXTENDED_ERROR_INFO3_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_EXTENDED_ERROR_INFO4_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[4];
      bus_FW_EXTENDED_ERROR_INFO4_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_EXTENDED_ERROR_INFO5_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[5];
      bus_FW_EXTENDED_ERROR_INFO5_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_EXTENDED_ERROR_INFO6_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[6];
      bus_FW_EXTENDED_ERROR_INFO6_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      FW_EXTENDED_ERROR_INFO7_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_EXTENDED_ERROR_INFO[7];
      bus_FW_EXTENDED_ERROR_INFO7_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_TIMER1_EN -----------------------
    covergroup mci_WDT_TIMER1_EN_cg (ref logic [1:0] bus_event) @(posedge clk);
      WDT_TIMER1_EN_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER1_EN;
      bus_WDT_TIMER1_EN_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_TIMER1_CTRL -----------------------
    covergroup mci_WDT_TIMER1_CTRL_cg (ref logic [1:0] bus_event) @(posedge clk);
      WDT_TIMER1_CTRL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER1_CTRL;
      bus_WDT_TIMER1_CTRL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_TIMER1_TIMEOUT_PERIOD [0:1] -----------------------
    covergroup mci_WDT_TIMER1_TIMEOUT_PERIOD_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      WDT_TIMER1_TIMEOUT_PERIOD0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER1_TIMEOUT_PERIOD[0];
      bus_WDT_TIMER1_TIMEOUT_PERIOD0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      WDT_TIMER1_TIMEOUT_PERIOD1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER1_TIMEOUT_PERIOD[1];
      bus_WDT_TIMER1_TIMEOUT_PERIOD1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_TIMER2_EN -----------------------
    covergroup mci_WDT_TIMER2_EN_cg (ref logic [1:0] bus_event) @(posedge clk);
      WDT_TIMER2_EN_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER2_EN;
      bus_WDT_TIMER2_EN_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_TIMER2_CTRL -----------------------
    covergroup mci_WDT_TIMER2_CTRL_cg (ref logic [1:0] bus_event) @(posedge clk);
      WDT_TIMER2_CTRL_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER2_CTRL;
      bus_WDT_TIMER2_CTRL_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_TIMER2_TIMEOUT_PERIOD [0:1] -----------------------
    covergroup mci_WDT_TIMER2_TIMEOUT_PERIOD_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      WDT_TIMER2_TIMEOUT_PERIOD0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER2_TIMEOUT_PERIOD[0];
      bus_WDT_TIMER2_TIMEOUT_PERIOD0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      WDT_TIMER2_TIMEOUT_PERIOD1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_TIMER2_TIMEOUT_PERIOD[1];
      bus_WDT_TIMER2_TIMEOUT_PERIOD1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_STATUS -----------------------
    covergroup mci_WDT_STATUS_cg (ref logic [1:0] bus_event) @(posedge clk);
      WDT_STATUS_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_STATUS;
      bus_WDT_STATUS_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP WDT_CFG [0:1] -----------------------
    covergroup mci_WDT_CFG_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      WDT_CFG0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_CFG[0];
      bus_WDT_CFG0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      WDT_CFG1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.WDT_CFG[1];
      bus_WDT_CFG1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCU_TIMER_CONFIG -----------------------
    covergroup mci_MCU_TIMER_CONFIG_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCU_TIMER_CONFIG_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCU_TIMER_CONFIG;
      bus_MCU_TIMER_CONFIG_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCU_RV_MTIME_L -----------------------
    covergroup mci_MCU_RV_MTIME_L_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCU_RV_MTIME_L_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCU_RV_MTIME_L;
      bus_MCU_RV_MTIME_L_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCU_RV_MTIME_H -----------------------
    covergroup mci_MCU_RV_MTIME_H_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCU_RV_MTIME_H_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCU_RV_MTIME_H;
      bus_MCU_RV_MTIME_H_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCU_RV_MTIMECMP_L -----------------------
    covergroup mci_MCU_RV_MTIMECMP_L_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCU_RV_MTIMECMP_L_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCU_RV_MTIMECMP_L;
      bus_MCU_RV_MTIMECMP_L_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCU_RV_MTIMECMP_H -----------------------
    covergroup mci_MCU_RV_MTIMECMP_H_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCU_RV_MTIMECMP_H_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCU_RV_MTIMECMP_H;
      bus_MCU_RV_MTIMECMP_H_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP RESET_REQUEST -----------------------
    covergroup mci_RESET_REQUEST_cg (ref logic [1:0] bus_event) @(posedge clk);
      RESET_REQUEST_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.RESET_REQUEST;
      bus_RESET_REQUEST_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCI_BOOTFSM_GO -----------------------
    covergroup mci_MCI_BOOTFSM_GO_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCI_BOOTFSM_GO_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCI_BOOTFSM_GO;
      bus_MCI_BOOTFSM_GO_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP CPTRA_BOOT_GO -----------------------
    covergroup mci_CPTRA_BOOT_GO_cg (ref logic [1:0] bus_event) @(posedge clk);
      CPTRA_BOOT_GO_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.CPTRA_BOOT_GO;
      bus_CPTRA_BOOT_GO_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP FW_SRAM_EXEC_REGION_SIZE -----------------------
    covergroup mci_FW_SRAM_EXEC_REGION_SIZE_cg (ref logic [1:0] bus_event) @(posedge clk);
      FW_SRAM_EXEC_REGION_SIZE_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FW_SRAM_EXEC_REGION_SIZE;
      bus_FW_SRAM_EXEC_REGION_SIZE_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCU_NMI_VECTOR -----------------------
    covergroup mci_MCU_NMI_VECTOR_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCU_NMI_VECTOR_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCU_NMI_VECTOR;
      bus_MCU_NMI_VECTOR_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MCU_RESET_VECTOR -----------------------
    covergroup mci_MCU_RESET_VECTOR_cg (ref logic [1:0] bus_event) @(posedge clk);
      MCU_RESET_VECTOR_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MCU_RESET_VECTOR;
      bus_MCU_RESET_VECTOR_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MBOX0_VALID_AXI_USER [0:4] -----------------------
    covergroup mci_MBOX0_VALID_AXI_USER_cg (ref logic [1:0] bus_event[0:4]) @(posedge clk);
      MBOX0_VALID_AXI_USER0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_VALID_AXI_USER[0];
      bus_MBOX0_VALID_AXI_USER0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_VALID_AXI_USER1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_VALID_AXI_USER[1];
      bus_MBOX0_VALID_AXI_USER1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_VALID_AXI_USER2_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_VALID_AXI_USER[2];
      bus_MBOX0_VALID_AXI_USER2_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_VALID_AXI_USER3_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_VALID_AXI_USER[3];
      bus_MBOX0_VALID_AXI_USER3_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_VALID_AXI_USER4_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_VALID_AXI_USER[4];
      bus_MBOX0_VALID_AXI_USER4_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MBOX0_AXI_USER_LOCK [0:4] -----------------------
    covergroup mci_MBOX0_AXI_USER_LOCK_cg (ref logic [1:0] bus_event[0:4]) @(posedge clk);
      MBOX0_AXI_USER_LOCK0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_AXI_USER_LOCK[0];
      bus_MBOX0_AXI_USER_LOCK0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_AXI_USER_LOCK1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_AXI_USER_LOCK[1];
      bus_MBOX0_AXI_USER_LOCK1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_AXI_USER_LOCK2_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_AXI_USER_LOCK[2];
      bus_MBOX0_AXI_USER_LOCK2_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_AXI_USER_LOCK3_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_AXI_USER_LOCK[3];
      bus_MBOX0_AXI_USER_LOCK3_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX0_AXI_USER_LOCK4_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX0_AXI_USER_LOCK[4];
      bus_MBOX0_AXI_USER_LOCK4_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP MBOX1_VALID_AXI_USER [0:4] -----------------------
    covergroup mci_MBOX1_VALID_AXI_USER_cg (ref logic [1:0] bus_event[0:4]) @(posedge clk);
      MBOX1_VALID_AXI_USER0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX1_VALID_AXI_USER[0];
      bus_MBOX1_VALID_AXI_USER0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX1_VALID_AXI_USER1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX1_VALID_AXI_USER[1];
      bus_MBOX1_VALID_AXI_USER1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX1_VALID_AXI_USER2_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX1_VALID_AXI_USER[2];
      bus_MBOX1_VALID_AXI_USER2_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX1_VALID_AXI_USER3_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX1_VALID_AXI_USER[3];
      bus_MBOX1_VALID_AXI_USER3_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      MBOX1_VALID_AXI_USER4_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.MBOX1_VALID_AXI_USER[4];
      bus_MBOX1_VALID_AXI_USER4_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP SOC_DFT_EN [0:1] -----------------------
    covergroup mci_SOC_DFT_EN_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      SOC_DFT_EN0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SOC_DFT_EN[0];
      bus_SOC_DFT_EN0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      SOC_DFT_EN1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SOC_DFT_EN[1];
      bus_SOC_DFT_EN1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP SOC_HW_DEBUG_EN [0:1] -----------------------
    covergroup mci_SOC_HW_DEBUG_EN_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      SOC_HW_DEBUG_EN0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SOC_HW_DEBUG_EN[0];
      bus_SOC_HW_DEBUG_EN0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      SOC_HW_DEBUG_EN1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SOC_HW_DEBUG_EN[1];
      bus_SOC_HW_DEBUG_EN1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP SOC_PROD_DEBUG_STATE [0:1] -----------------------
    covergroup mci_SOC_PROD_DEBUG_STATE_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      SOC_PROD_DEBUG_STATE0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SOC_PROD_DEBUG_STATE[0];
      bus_SOC_PROD_DEBUG_STATE0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      SOC_PROD_DEBUG_STATE1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SOC_PROD_DEBUG_STATE[1];
      bus_SOC_PROD_DEBUG_STATE1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP FC_FIPS_ZEROZATION -----------------------
    covergroup mci_FC_FIPS_ZEROZATION_cg (ref logic [1:0] bus_event) @(posedge clk);
      FC_FIPS_ZEROZATION_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.FC_FIPS_ZEROZATION;
      bus_FC_FIPS_ZEROZATION_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP GENERIC_INPUT_WIRES [0:1] -----------------------
    covergroup mci_GENERIC_INPUT_WIRES_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      GENERIC_INPUT_WIRES0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.GENERIC_INPUT_WIRES[0];
      bus_GENERIC_INPUT_WIRES0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      GENERIC_INPUT_WIRES1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.GENERIC_INPUT_WIRES[1];
      bus_GENERIC_INPUT_WIRES1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP GENERIC_OUTPUT_WIRES [0:1] -----------------------
    covergroup mci_GENERIC_OUTPUT_WIRES_cg (ref logic [1:0] bus_event[0:1]) @(posedge clk);
      GENERIC_OUTPUT_WIRES0_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.GENERIC_OUTPUT_WIRES[0];
      bus_GENERIC_OUTPUT_WIRES0_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      GENERIC_OUTPUT_WIRES1_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.GENERIC_OUTPUT_WIRES[1];
      bus_GENERIC_OUTPUT_WIRES1_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP DEBUG_IN -----------------------
    covergroup mci_DEBUG_IN_cg (ref logic [1:0] bus_event) @(posedge clk);
      DEBUG_IN_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.DEBUG_IN;
      bus_DEBUG_IN_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP DEBUG_OUT -----------------------
    covergroup mci_DEBUG_OUT_cg (ref logic [1:0] bus_event) @(posedge clk);
      DEBUG_OUT_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.DEBUG_OUT;
      bus_DEBUG_OUT_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP SS_DEBUG_INTENT -----------------------
    covergroup mci_SS_DEBUG_INTENT_cg (ref logic [1:0] bus_event) @(posedge clk);
      SS_DEBUG_INTENT_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SS_DEBUG_INTENT;
      bus_SS_DEBUG_INTENT_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP SS_CONFIG_DONE_STICKY -----------------------
    covergroup mci_SS_CONFIG_DONE_STICKY_cg (ref logic [1:0] bus_event) @(posedge clk);
      SS_CONFIG_DONE_STICKY_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SS_CONFIG_DONE_STICKY;
      bus_SS_CONFIG_DONE_STICKY_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP SS_CONFIG_DONE -----------------------
    covergroup mci_SS_CONFIG_DONE_cg (ref logic [1:0] bus_event) @(posedge clk);
      SS_CONFIG_DONE_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.SS_CONFIG_DONE;
      bus_SS_CONFIG_DONE_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_0 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_00_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_00_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_01_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_01_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_02_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_02_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_03_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_03_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_04_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_04_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_05_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_05_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_06_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_06_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_07_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_07_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_08_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_08_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_09_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_09_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_010_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_010_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_011_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[0][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_011_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_1 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_10_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_10_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_11_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_11_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_12_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_12_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_13_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_13_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_14_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_14_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_15_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_15_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_16_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_16_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_17_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_17_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_18_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_18_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_19_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_19_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_110_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_110_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_111_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[1][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_111_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_2 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_20_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_20_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_21_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_21_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_22_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_22_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_23_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_23_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_24_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_24_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_25_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_25_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_26_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_26_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_27_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_27_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_28_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_28_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_29_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_29_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_210_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_210_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_211_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[2][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_211_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_3 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_30_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_30_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_31_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_31_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_32_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_32_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_33_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_33_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_34_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_34_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_35_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_35_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_36_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_36_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_37_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_37_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_38_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_38_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_39_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_39_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_310_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_310_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_311_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[3][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_311_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_4 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_40_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_40_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_41_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_41_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_42_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_42_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_43_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_43_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_44_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_44_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_45_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_45_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_46_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_46_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_47_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_47_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_48_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_48_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_49_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_49_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_410_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_410_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_411_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[4][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_411_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_5 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_50_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_50_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_51_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_51_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_52_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_52_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_53_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_53_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_54_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_54_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_55_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_55_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_56_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_56_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_57_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_57_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_58_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_58_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_59_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_59_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_510_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_510_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_511_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[5][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_511_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_6 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_60_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_60_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_61_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_61_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_62_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_62_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_63_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_63_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_64_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_64_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_65_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_65_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_66_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_66_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_67_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_67_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_68_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_68_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_69_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_69_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_610_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_610_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_611_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[6][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_611_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP PROD_DEBUG_UNLOCK_PK_HASH_REG_7 [0:11] -----------------------
    covergroup mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_cg (ref logic [1:0] bus_event[0:11]) @(posedge clk);
      PROD_DEBUG_UNLOCK_PK_HASH_REG_70_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][0];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_70_cp : coverpoint bus_event[0] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_71_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][1];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_71_cp : coverpoint bus_event[1] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_72_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][2];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_72_cp : coverpoint bus_event[2] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_73_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][3];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_73_cp : coverpoint bus_event[3] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_74_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][4];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_74_cp : coverpoint bus_event[4] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_75_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][5];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_75_cp : coverpoint bus_event[5] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_76_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][6];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_76_cp : coverpoint bus_event[6] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_77_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][7];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_77_cp : coverpoint bus_event[7] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_78_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][8];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_78_cp : coverpoint bus_event[8] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_79_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][9];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_79_cp : coverpoint bus_event[9] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_710_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][10];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_710_cp : coverpoint bus_event[10] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
      PROD_DEBUG_UNLOCK_PK_HASH_REG_711_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.PROD_DEBUG_UNLOCK_PK_HASH_REG[7][11];
      bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_711_cp : coverpoint bus_event[11] {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_GLOBAL_INTR_EN_R -----------------------
    covergroup mci_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_GLOBAL_INTR_EN_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.global_intr_en_r;
      bus_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR0_INTR_EN_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR0_INTR_EN_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR0_INTR_EN_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error0_intr_en_r;
      bus_INTR_BLOCK_RF_ERROR0_INTR_EN_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR1_INTR_EN_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR1_INTR_EN_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR1_INTR_EN_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error1_intr_en_r;
      bus_INTR_BLOCK_RF_ERROR1_INTR_EN_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF0_INTR_EN_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF0_INTR_EN_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif0_intr_en_r;
      bus_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF1_INTR_EN_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF1_INTR_EN_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif1_intr_en_r;
      bus_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_global_intr_r;
      bus_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_global_intr_r;
      bus_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error0_internal_intr_r;
      bus_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error1_internal_intr_r;
      bus_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif0_internal_intr_r;
      bus_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif1_internal_intr_r;
      bus_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR0_INTR_TRIG_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error0_intr_trig_r;
      bus_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR1_INTR_TRIG_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error1_intr_trig_r;
      bus_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif0_intr_trig_r;
      bus_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif1_intr_trig_r;
      bus_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_internal_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_mbox0_ecc_unc_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_mbox1_ecc_unc_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_mcu_sram_dmi_axi_collision_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_wdt_timer1_timeout_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_wdt_timer2_timeout_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal0_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal1_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal2_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal3_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal4_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal5_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal6_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal7_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal8_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal9_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal10_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal11_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal12_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal13_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal14_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal15_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal16_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal17_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal18_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal19_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal20_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal21_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal22_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal23_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal24_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal25_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal26_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal27_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal28_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal29_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal30_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal31_intr_count_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mcu_sram_ecc_cor_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_cptra_mcu_reset_req_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_gen_in_toggle_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal0_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal1_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal2_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal3_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal4_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal5_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal6_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal7_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal8_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal9_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal10_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal11_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal12_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal13_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal14_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal15_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal16_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal17_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal18_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal19_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal20_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal21_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal22_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal23_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal24_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal25_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal26_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal27_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal28_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal29_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal30_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal31_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_target_done_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_target_done_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_cmd_avail_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_cmd_avail_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_cptra_mbox_cmd_avail_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_ecc_cor_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_ecc_cor_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_debug_locked_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_scan_mode_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_soc_req_lock_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_soc_req_lock_intr_count_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_internal_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_mbox0_ecc_unc_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_mbox1_ecc_unc_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_wdt_timer1_timeout_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_wdt_timer2_timeout_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_mcu_sram_dmi_axi_collision_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal0_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal1_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal2_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal3_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal4_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal5_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal6_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal7_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal8_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal9_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal10_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal11_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal12_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal13_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal14_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal15_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal16_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal17_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal18_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal19_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal20_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal21_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal22_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal23_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal24_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal25_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal26_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal27_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal28_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal29_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal30_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.error_agg_error_fatal31_intr_count_incr_r;
      bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mcu_sram_ecc_cor_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_cptra_mcu_reset_req_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_gen_in_toggle_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal0_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal1_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal2_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal3_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal4_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal5_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal6_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal7_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal8_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal9_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal10_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal11_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal12_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal13_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal14_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal15_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal16_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal17_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal18_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal19_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal20_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal21_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal22_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal23_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal24_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal25_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal26_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal27_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal28_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal29_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal30_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_agg_error_non_fatal31_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_target_done_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_target_done_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_cmd_avail_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_cmd_avail_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_cptra_mbox_cmd_avail_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_ecc_cor_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_ecc_cor_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_debug_locked_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_scan_mode_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox0_soc_req_lock_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
    // ----------------------- COVERGROUP INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R -----------------------
    covergroup mci_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cg (ref logic [1:0] bus_event) @(posedge clk);
      INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cp : coverpoint i_mci_reg_top.i_mci_reg.field_storage.intr_block_rf.notif_mbox1_soc_req_lock_intr_count_incr_r;
      bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cp : coverpoint bus_event {
        bins rd = {AXI_RD};
        bins wr = {AXI_WR};
        ignore_bins dont_care = {IDLE, 2'h3};
      }
    endgroup
  
  
    // ----------------------- COVERGROUP Instantiations -----------------------
  
    mci_HW_CAPABILITIES_cg HW_CAPABILITIES_cg = new(bus_HW_CAPABILITIES);
    mci_FW_CAPABILITIES_cg FW_CAPABILITIES_cg = new(bus_FW_CAPABILITIES);
    mci_CAP_LOCK_cg CAP_LOCK_cg = new(bus_CAP_LOCK);
    // mci_HW_REV_ID_cg HW_REV_ID_cg = new(bus_HW_REV_ID);
    mci_FW_REV_ID_cg FW_REV_ID_cg = new(bus_FW_REV_ID);
    // mci_HW_CONFIG0_cg HW_CONFIG0_cg = new(bus_HW_CONFIG0);
    // mci_HW_CONFIG1_cg HW_CONFIG1_cg = new(bus_HW_CONFIG1);
    mci_FW_FLOW_STATUS_cg FW_FLOW_STATUS_cg = new(bus_FW_FLOW_STATUS);
    mci_HW_FLOW_STATUS_cg HW_FLOW_STATUS_cg = new(bus_HW_FLOW_STATUS);
    mci_RESET_REASON_cg RESET_REASON_cg = new(bus_RESET_REASON);
    mci_RESET_STATUS_cg RESET_STATUS_cg = new(bus_RESET_STATUS);
    // mci_SECURITY_STATE_cg SECURITY_STATE_cg = new(bus_SECURITY_STATE);
    mci_HW_ERROR_FATAL_cg HW_ERROR_FATAL_cg = new(bus_HW_ERROR_FATAL);
    mci_AGG_ERROR_FATAL_cg AGG_ERROR_FATAL_cg = new(bus_AGG_ERROR_FATAL);
    mci_HW_ERROR_NON_FATAL_cg HW_ERROR_NON_FATAL_cg = new(bus_HW_ERROR_NON_FATAL);
    mci_AGG_ERROR_NON_FATAL_cg AGG_ERROR_NON_FATAL_cg = new(bus_AGG_ERROR_NON_FATAL);
    mci_FW_ERROR_FATAL_cg FW_ERROR_FATAL_cg = new(bus_FW_ERROR_FATAL);
    mci_FW_ERROR_NON_FATAL_cg FW_ERROR_NON_FATAL_cg = new(bus_FW_ERROR_NON_FATAL);
    mci_HW_ERROR_ENC_cg HW_ERROR_ENC_cg = new(bus_HW_ERROR_ENC);
    mci_FW_ERROR_ENC_cg FW_ERROR_ENC_cg = new(bus_FW_ERROR_ENC);
    mci_FW_EXTENDED_ERROR_INFO_cg FW_EXTENDED_ERROR_INFO_cg = new(bus_FW_EXTENDED_ERROR_INFO);
    mci_WDT_TIMER1_EN_cg WDT_TIMER1_EN_cg = new(bus_WDT_TIMER1_EN);
    mci_WDT_TIMER1_CTRL_cg WDT_TIMER1_CTRL_cg = new(bus_WDT_TIMER1_CTRL);
    mci_WDT_TIMER1_TIMEOUT_PERIOD_cg WDT_TIMER1_TIMEOUT_PERIOD_cg = new(bus_WDT_TIMER1_TIMEOUT_PERIOD);
    mci_WDT_TIMER2_EN_cg WDT_TIMER2_EN_cg = new(bus_WDT_TIMER2_EN);
    mci_WDT_TIMER2_CTRL_cg WDT_TIMER2_CTRL_cg = new(bus_WDT_TIMER2_CTRL);
    mci_WDT_TIMER2_TIMEOUT_PERIOD_cg WDT_TIMER2_TIMEOUT_PERIOD_cg = new(bus_WDT_TIMER2_TIMEOUT_PERIOD);
    mci_WDT_STATUS_cg WDT_STATUS_cg = new(bus_WDT_STATUS);
    mci_WDT_CFG_cg WDT_CFG_cg = new(bus_WDT_CFG);
    mci_MCU_TIMER_CONFIG_cg MCU_TIMER_CONFIG_cg = new(bus_MCU_TIMER_CONFIG);
    mci_MCU_RV_MTIME_L_cg MCU_RV_MTIME_L_cg = new(bus_MCU_RV_MTIME_L);
    mci_MCU_RV_MTIME_H_cg MCU_RV_MTIME_H_cg = new(bus_MCU_RV_MTIME_H);
    mci_MCU_RV_MTIMECMP_L_cg MCU_RV_MTIMECMP_L_cg = new(bus_MCU_RV_MTIMECMP_L);
    mci_MCU_RV_MTIMECMP_H_cg MCU_RV_MTIMECMP_H_cg = new(bus_MCU_RV_MTIMECMP_H);
    mci_RESET_REQUEST_cg RESET_REQUEST_cg = new(bus_RESET_REQUEST);
    mci_MCI_BOOTFSM_GO_cg MCI_BOOTFSM_GO_cg = new(bus_MCI_BOOTFSM_GO);
    mci_CPTRA_BOOT_GO_cg CPTRA_BOOT_GO_cg = new(bus_CPTRA_BOOT_GO);
    mci_FW_SRAM_EXEC_REGION_SIZE_cg FW_SRAM_EXEC_REGION_SIZE_cg = new(bus_FW_SRAM_EXEC_REGION_SIZE);
    mci_MCU_NMI_VECTOR_cg MCU_NMI_VECTOR_cg = new(bus_MCU_NMI_VECTOR);
    mci_MCU_RESET_VECTOR_cg MCU_RESET_VECTOR_cg = new(bus_MCU_RESET_VECTOR);
    mci_MBOX0_VALID_AXI_USER_cg MBOX0_VALID_AXI_USER_cg = new(bus_MBOX0_VALID_AXI_USER);
    mci_MBOX0_AXI_USER_LOCK_cg MBOX0_AXI_USER_LOCK_cg = new(bus_MBOX0_AXI_USER_LOCK);
    mci_MBOX1_VALID_AXI_USER_cg MBOX1_VALID_AXI_USER_cg = new(bus_MBOX1_VALID_AXI_USER);
    mci_SOC_DFT_EN_cg SOC_DFT_EN_cg = new(bus_SOC_DFT_EN);
    mci_SOC_HW_DEBUG_EN_cg SOC_HW_DEBUG_EN_cg = new(bus_SOC_HW_DEBUG_EN);
    mci_SOC_PROD_DEBUG_STATE_cg SOC_PROD_DEBUG_STATE_cg = new(bus_SOC_PROD_DEBUG_STATE);
    mci_FC_FIPS_ZEROZATION_cg FC_FIPS_ZEROZATION_cg = new(bus_FC_FIPS_ZEROZATION);
    mci_GENERIC_INPUT_WIRES_cg GENERIC_INPUT_WIRES_cg = new(bus_GENERIC_INPUT_WIRES);
    mci_GENERIC_OUTPUT_WIRES_cg GENERIC_OUTPUT_WIRES_cg = new(bus_GENERIC_OUTPUT_WIRES);
    mci_DEBUG_IN_cg DEBUG_IN_cg = new(bus_DEBUG_IN);
    mci_DEBUG_OUT_cg DEBUG_OUT_cg = new(bus_DEBUG_OUT);
    mci_SS_DEBUG_INTENT_cg SS_DEBUG_INTENT_cg = new(bus_SS_DEBUG_INTENT);
    mci_SS_CONFIG_DONE_STICKY_cg SS_CONFIG_DONE_STICKY_cg = new(bus_SS_CONFIG_DONE_STICKY);
    mci_SS_CONFIG_DONE_cg SS_CONFIG_DONE_cg = new(bus_SS_CONFIG_DONE);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_0_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_0_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_0);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_1_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_1_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_1);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_2_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_2_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_2);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_3_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_3_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_3);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_4_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_4_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_4);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_5_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_5_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_5);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_6_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_6_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_6);
    mci_PROD_DEBUG_UNLOCK_PK_HASH_REG_7_cg PROD_DEBUG_UNLOCK_PK_HASH_REG_7_cg = new(bus_PROD_DEBUG_UNLOCK_PK_HASH_REG_7);
    mci_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_cg INTR_BLOCK_RF_GLOBAL_INTR_EN_R_cg = new(bus_INTR_BLOCK_RF_GLOBAL_INTR_EN_R);
    mci_INTR_BLOCK_RF_ERROR0_INTR_EN_R_cg INTR_BLOCK_RF_ERROR0_INTR_EN_R_cg = new(bus_INTR_BLOCK_RF_ERROR0_INTR_EN_R);
    mci_INTR_BLOCK_RF_ERROR1_INTR_EN_R_cg INTR_BLOCK_RF_ERROR1_INTR_EN_R_cg = new(bus_INTR_BLOCK_RF_ERROR1_INTR_EN_R);
    mci_INTR_BLOCK_RF_NOTIF0_INTR_EN_R_cg INTR_BLOCK_RF_NOTIF0_INTR_EN_R_cg = new(bus_INTR_BLOCK_RF_NOTIF0_INTR_EN_R);
    mci_INTR_BLOCK_RF_NOTIF1_INTR_EN_R_cg INTR_BLOCK_RF_NOTIF1_INTR_EN_R_cg = new(bus_INTR_BLOCK_RF_NOTIF1_INTR_EN_R);
    mci_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_cg INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R);
    mci_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_cg INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R);
    mci_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_cg INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R_cg = new(bus_INTR_BLOCK_RF_ERROR0_INTERNAL_INTR_R);
    mci_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_cg INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R_cg = new(bus_INTR_BLOCK_RF_ERROR1_INTERNAL_INTR_R);
    mci_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_cg INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF0_INTERNAL_INTR_R);
    mci_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_cg INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF1_INTERNAL_INTR_R);
    mci_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_cg INTR_BLOCK_RF_ERROR0_INTR_TRIG_R_cg = new(bus_INTR_BLOCK_RF_ERROR0_INTR_TRIG_R);
    mci_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_cg INTR_BLOCK_RF_ERROR1_INTR_TRIG_R_cg = new(bus_INTR_BLOCK_RF_ERROR1_INTR_TRIG_R);
    mci_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_cg INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R_cg = new(bus_INTR_BLOCK_RF_NOTIF0_INTR_TRIG_R);
    mci_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_cg INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R_cg = new(bus_INTR_BLOCK_RF_NOTIF1_INTR_TRIG_R);
    mci_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_R);
    mci_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_MBOX0_ECC_UNC_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_MBOX1_ECC_UNC_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_MCU_SRAM_DMI_AXI_COLLISION_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL0_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL1_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL2_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL3_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL4_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL5_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL6_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL7_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL8_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL9_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL10_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL11_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL12_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL13_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL14_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL15_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL16_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL17_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL18_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL19_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL20_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL21_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL22_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL23_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL24_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL25_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL26_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL27_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL28_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL29_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL30_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_ERROR_AGG_ERROR_FATAL31_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MCU_SRAM_ECC_COR_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_CPTRA_MCU_RESET_REQ_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL0_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL1_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL2_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL3_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL4_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL5_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL6_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL7_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL8_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL9_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL10_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL11_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL12_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL13_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL14_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL15_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL16_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL17_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL18_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL19_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL20_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL21_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL22_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL23_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL24_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL25_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL26_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL27_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL28_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL29_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL30_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_AGG_ERROR_NON_FATAL31_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_TARGET_DONE_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_TARGET_DONE_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_CMD_AVAIL_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_CMD_AVAIL_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_CPTRA_MBOX_CMD_AVAIL_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_ECC_COR_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_ECC_COR_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX0_SOC_REQ_LOCK_INTR_COUNT_INCR_R);
    mci_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cg INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R_cg = new(bus_INTR_BLOCK_RF_NOTIF_MBOX1_SOC_REQ_LOCK_INTR_COUNT_INCR_R);
  
    // ------------------------------------------------------------------- 
    // end SCRIPT_OUTPUT
    // ------------------------------------------------------------------- 
  
  endinterface
  
  
  `endif
