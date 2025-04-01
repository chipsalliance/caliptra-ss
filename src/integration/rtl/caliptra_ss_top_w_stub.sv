`include "caliptra_ss_includes.svh"

module caliptra_ss_top_w_stub();

    import axi_pkg::*;
    import soc_ifc_pkg::*;
    import css_mcu0_el2_pkg::*;
    
    `include "css_mcu0_el2_param.vh"
    // Define the logic and interfaces
    logic cptra_ss_clk_i;
    logic cptra_ss_pwrgood_i;
    logic cptra_ss_rst_b_i;
    logic cptra_ss_mci_cptra_rst_b_o;

    axi_if cptra_ss_cptra_core_s_axi_if(.clk(cptra_ss_clk_i), .rst_n(cptra_ss_rst_b_i));
    axi_if cptra_ss_cptra_core_m_axi_if(.clk(cptra_ss_clk_i), .rst_n(cptra_ss_rst_b_i));
    axi_if cptra_ss_mci_s_axi_if(.clk(cptra_ss_clk_i), .rst_n(cptra_ss_rst_b_i));
    axi_if cptra_ss_mcu_rom_s_axi_if(.clk(cptra_ss_clk_i), .rst_n(cptra_ss_rst_b_i));
    axi_mem_if mcu_rom_mem_export_if(.clk(cptra_ss_clk_i), .rst_b(cptra_ss_rst_b_i));
    axi_if cptra_ss_mcu_lsu_m_axi_if(.clk(cptra_ss_clk_i), .rst_n(cptra_ss_rst_b_i));
    axi_if cptra_ss_mcu_ifu_m_axi_if(.clk(cptra_ss_clk_i), .rst_n(cptra_ss_rst_b_i));
    axi_if cptra_ss_i3c_s_axi_if(.clk(cptra_ss_clk_i), .rst_n(cptra_ss_rst_b_i));

    axi_struct_pkg::axi_wr_req_t cptra_ss_lc_axi_wr_req_i;
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_lc_axi_wr_rsp_o;
    axi_struct_pkg::axi_rd_req_t cptra_ss_lc_axi_rd_req_i;
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_lc_axi_rd_rsp_o;

    axi_struct_pkg::axi_wr_req_t cptra_ss_otp_core_axi_wr_req_i;
    axi_struct_pkg::axi_wr_rsp_t cptra_ss_otp_core_axi_wr_rsp_o;
    axi_struct_pkg::axi_rd_req_t cptra_ss_otp_core_axi_rd_req_i;
    axi_struct_pkg::axi_rd_rsp_t cptra_ss_otp_core_axi_rd_rsp_o;

    logic [255:0] cptra_ss_cptra_obf_key_i;
    logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0] cptra_ss_cptra_csr_hmac_key_i;

    logic cptra_ss_cptra_core_jtag_tck_i;
    logic cptra_ss_cptra_core_jtag_tms_i;
    logic cptra_ss_cptra_core_jtag_tdi_i;
    logic cptra_ss_cptra_core_jtag_trst_n_i;
    logic cptra_ss_cptra_core_jtag_tdo_o;
    logic cptra_ss_cptra_core_jtag_tdoEn_o;
    logic [124:0] cptra_ss_cptra_generic_fw_exec_ctrl_o;
    logic cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o;

    jtag_pkg::jtag_req_t cptra_ss_lc_ctrl_jtag_i;
    jtag_pkg::jtag_rsp_t cptra_ss_lc_ctrl_jtag_o;

    el2_mem_if cptra_ss_cptra_core_el2_mem_export();
    mldsa_mem_if mldsa_memory_export();


    logic cptra_ss_cptra_core_mbox_sram_cs_o;
    logic cptra_ss_cptra_core_mbox_sram_we_o;
    logic [CPTRA_MBOX_ADDR_W-1:0] cptra_sscptra_core_mbox_sram_addr_o;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_ss_cptra_core_mbox_sram_wdata_o;
    logic [CPTRA_MBOX_DATA_AND_ECC_W-1:0] cptra_ss_cptra_core_mbox_sram_rdata_i;

    logic cptra_ss_cptra_core_imem_cs_o;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] cptra_ss_cptra_core_imem_addr_o;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] cptra_ss_cptra_core_imem_rdata_i;

    logic cptra_ss_cptra_core_bootfsm_bp_i;

`ifdef CALIPTRA_INTERNAL_TRNG
    logic cptra_ss_cptra_core_etrng_req_o;
    logic [3:0] cptra_ss_cptra_core_itrng_data_i;
    logic cptra_ss_cptra_core_itrng_valid_i;
`endif

    logic [CPTRA_SS_MCU_USER_WIDTH-1:0] cptra_ss_strap_mcu_lsu_axi_user_i;
    logic [CPTRA_SS_MCU_USER_WIDTH-1:0] cptra_ss_strap_mcu_ifu_axi_user_i;
    logic [CPTRA_SS_MCU_USER_WIDTH-1:0] cptra_ss_strap_mcu_sram_config_axi_user_i;
    logic [CPTRA_SS_MCU_USER_WIDTH-1:0] cptra_ss_strap_mci_soc_config_axi_user_i;
    
    mci_mcu_sram_if cptra_ss_mci_mcu_sram_req_if(
        .clk(cptra_ss_clk_i),
        .rst_b(cptra_ss_rst_b_i)
    );
    mci_mcu_sram_if cptra_ss_mcu_mbox0_sram_req_if(
        .clk(cptra_ss_clk_i),
        .rst_b(cptra_ss_rst_b_i)
    );
    mci_mcu_sram_if cptra_ss_mcu_mbox1_sram_req_if(
        .clk(cptra_ss_clk_i),
        .rst_b(cptra_ss_rst_b_i)
    );

    css_mcu0_el2_mem_if cptra_ss_mcu0_el2_mem_export();

    logic cptra_ss_soc_mcu_mbox0_data_avail;
    logic cptra_ss_soc_mcu_mbox1_data_avail;

    logic [63:0] cptra_ss_mci_generic_input_wires_i;

    logic [31:0] cptra_ss_strap_mcu_reset_vector_i;
    logic cptra_ss_mcu_no_rom_config_i;
    logic cptra_ss_mci_boot_seq_brkpoint_i;

    logic cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i;
    logic cptra_ss_FIPS_ZEROIZATION_PPD_i;

    logic [63:0] cptra_ss_mci_generic_output_wires_o;
    logic cptra_ss_all_error_fatal_o;
    logic cptra_ss_all_error_non_fatal_o;

    logic [pt.PIC_TOTAL_INT:`VEER_INTR_EXT_LSB] cptra_ss_mcu_ext_int;

    logic cptra_ss_mcu_jtag_tck_i;
    logic cptra_ss_mcu_jtag_tms_i;
    logic cptra_ss_mcu_jtag_tdi_i;
    logic cptra_ss_mcu_jtag_trst_n_i;
    logic cptra_ss_mcu_jtag_tdo_o;
    logic cptra_ss_mcu_jtag_tdoEn_o;

    logic [63:0] cptra_ss_strap_caliptra_base_addr_i;
    logic [63:0] cptra_ss_strap_mci_base_addr_i;
    logic [63:0] cptra_ss_strap_recovery_ifc_base_addr_i;
    logic [63:0] cptra_ss_strap_otp_fc_base_addr_i;
    logic [63:0] cptra_ss_strap_uds_seed_base_addr_i;
    logic [31:0] cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i;
    logic [31:0] cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i;
    logic [31:0] cptra_ss_strap_caliptra_dma_axi_user_i;
    logic [31:0] cptra_ss_strap_generic_0_i;
    logic [31:0] cptra_ss_strap_generic_1_i;
    logic [31:0] cptra_ss_strap_generic_2_i;
    logic [31:0] cptra_ss_strap_generic_3_i;
    logic cptra_ss_debug_intent_i;

    logic cptra_ss_dbg_manuf_enable_o;
    logic [63:0] cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o;

    lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_ack_i;
    lc_ctrl_pkg::lc_tx_t cptra_ss_lc_clk_byp_req_o;
    logic cptra_ss_lc_ctrl_scan_rst_ni_i;

    logic cptra_ss_lc_esclate_scrap_state0_i;
    logic cptra_ss_lc_esclate_scrap_state1_i;

    wire cptra_ss_soc_dft_en_o;
    wire cptra_ss_soc_hw_debug_en_o;

    otp_ctrl_pkg::prim_generic_otp_outputs_t      cptra_ss_fuse_macro_outputs_i;
    otp_ctrl_pkg::prim_generic_otp_inputs_t      cptra_ss_fuse_macro_inputs_o;

`ifdef DIGITAL_IO_I3C
    logic cptra_ss_i3c_scl_i;
    logic cptra_ss_i3c_sda_i;
    logic cptra_ss_i3c_scl_o;
    logic cptra_ss_i3c_sda_o;
    logic cptra_ss_sel_od_pp_o;
`else
    wire cptra_ss_i3c_scl_io;
    wire cptra_ss_i3c_sda_io;
`endif

    logic [63:0] cptra_ss_cptra_core_generic_input_wires_i;
    logic cptra_ss_cptra_core_scan_mode_i;
    logic cptra_error_fatal;
    logic cptra_error_non_fatal;
    logic ready_for_fuses;
    logic ready_for_mb_processing;
    logic mailbox_data_avail;

    initial begin
        cptra_ss_clk_i = '0;
        cptra_ss_pwrgood_i = '0;
        cptra_ss_rst_b_i = '0;
        cptra_ss_lc_axi_wr_req_i = '0;
        cptra_ss_lc_axi_rd_req_i = '0;
        cptra_ss_otp_core_axi_wr_req_i = '0;
        cptra_ss_otp_core_axi_rd_req_i = '0;
        cptra_ss_cptra_obf_key_i = '0;
        cptra_ss_cptra_csr_hmac_key_i = '0;
        cptra_ss_cptra_core_jtag_tck_i = '0;
        cptra_ss_cptra_core_jtag_tms_i = '0;
        cptra_ss_cptra_core_jtag_tdi_i = '0;
        cptra_ss_cptra_core_jtag_trst_n_i = '0;
        cptra_ss_cptra_core_bootfsm_bp_i = '0;
    `ifdef CALIPTRA_INTERNAL_TRNG
        cptra_ss_cptra_core_itrng_data_i = '0;
        cptra_ss_cptra_core_itrng_valid_i = '0;
    `endif
        cptra_ss_strap_mcu_lsu_axi_user_i = '0;
        cptra_ss_strap_mcu_ifu_axi_user_i = '0;
        cptra_ss_strap_mcu_sram_config_axi_user_i = '0;
        cptra_ss_strap_mci_soc_config_axi_user_i = '0;
        cptra_ss_mci_generic_input_wires_i = '0;
        cptra_ss_strap_mcu_reset_vector_i = '0;
        cptra_ss_mcu_no_rom_config_i = '0;
        cptra_ss_mci_boot_seq_brkpoint_i = '0;
        cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i = '0;
        cptra_ss_FIPS_ZEROIZATION_PPD_i = '0;
        cptra_ss_mcu_ext_int = (pt.PIC_TOTAL_INT+1-`VEER_INTR_EXT_LSB)'(0);
        cptra_ss_mcu_jtag_tck_i = '0;
        cptra_ss_mcu_jtag_tms_i = '0;
        cptra_ss_mcu_jtag_tdi_i = '0;
        cptra_ss_mcu_jtag_trst_n_i = '0;
        cptra_ss_strap_caliptra_base_addr_i = '0;
        cptra_ss_strap_mci_base_addr_i = '0;
        cptra_ss_strap_recovery_ifc_base_addr_i = '0;
        cptra_ss_strap_otp_fc_base_addr_i = '0;
        cptra_ss_strap_uds_seed_base_addr_i = '0;
        cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i = '0;
        cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i = '0;
        cptra_ss_strap_caliptra_dma_axi_user_i = '0;
        cptra_ss_strap_generic_0_i = '0;
        cptra_ss_strap_generic_1_i = '0;
        cptra_ss_strap_generic_2_i = '0;
        cptra_ss_strap_generic_3_i = '0;
        cptra_ss_debug_intent_i = '0;
        cptra_ss_lc_clk_byp_ack_i = '0;
        cptra_ss_lc_ctrl_scan_rst_ni_i = '0;
        cptra_ss_lc_esclate_scrap_state0_i = '0;
        cptra_ss_lc_esclate_scrap_state1_i = '0;
    `ifdef DIGITAL_IO_I3C
        cptra_ss_i3c_scl_i = '0;
        cptra_ss_i3c_sda_i = '0;
    `endif


        
    end

    // assign cptra_ss_cptra_core_el2_mem_export.veer_sram_sink = '0;
    // assign cptra_ss_mcu0_el2_mem_export.veer_sram_sink = '0;
    // assign cptra_ss_mci_mcu_sram_req_if.request = '0;
    // assign cptra_ss_mci_mbox0_sram_req_if.request = '0;
    // assign cptra_ss_mci_mbox1_sram_req_if.request = '0;
    // assign mldsa_memory_export_req.req = '0;

    caliptra_ss_top
    caliptra_ss_dut (

        .cptra_ss_clk_i(cptra_ss_clk_i),
        .cptra_ss_pwrgood_i(cptra_ss_pwrgood_i), //fixme
        .cptra_ss_rst_b_i(cptra_ss_rst_b_i), //fixme
        .cptra_ss_mci_cptra_rst_b_i(cptra_ss_mci_cptra_rst_b_o),
        .cptra_ss_mci_cptra_rst_b_o(cptra_ss_mci_cptra_rst_b_o),
    
    //SoC AXI Interface
        .cptra_ss_cptra_core_s_axi_if,
    
    // AXI Manager INF
        .cptra_ss_cptra_core_m_axi_if,
    
    //MCU ROM Sub Interface
        .cptra_ss_mcu_rom_s_axi_if,
        .mcu_rom_mem_export_if,
    
    //MCI AXI Sub Interface
        .cptra_ss_mci_s_axi_if,
    
        .cptra_ss_mcu_lsu_m_axi_if,
        .cptra_ss_mcu_ifu_m_axi_if,
        // .mcu_dma_s_axi_if,
        .cptra_ss_i3c_s_axi_if,
    
        .cptra_ss_lc_axi_wr_req_i,
        .cptra_ss_lc_axi_wr_rsp_o,
        .cptra_ss_lc_axi_rd_req_i,
        .cptra_ss_lc_axi_rd_rsp_o,
    
        .cptra_ss_otp_core_axi_wr_req_i,
        .cptra_ss_otp_core_axi_wr_rsp_o,
        .cptra_ss_otp_core_axi_rd_req_i,
        .cptra_ss_otp_core_axi_rd_rsp_o,
    
    //--------------------
    //caliptra core signals
    //--------------------
        .cptra_ss_cptra_obf_key_i,
        .cptra_ss_cptra_csr_hmac_key_i,  
    
    //Caliptra JTAG Interface
        .cptra_ss_cptra_core_jtag_tck_i,    // JTAG clk
        .cptra_ss_cptra_core_jtag_tms_i,    // JTAG TMS
        .cptra_ss_cptra_core_jtag_tdi_i,    // JTAG tdi
        .cptra_ss_cptra_core_jtag_trst_n_i, // JTAG Reset
        .cptra_ss_cptra_core_jtag_tdo_o,    // JTAG TDO
        .cptra_ss_cptra_core_jtag_tdoEn_o,  // JTAG TDO enable
        .cptra_ss_cptra_generic_fw_exec_ctrl_o,
        .cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o(cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o),
        .cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_i(cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_o),

    // LC Controller JTAG
        .cptra_ss_lc_ctrl_jtag_i,
        .cptra_ss_lc_ctrl_jtag_o,

    // Caliptra Memory Export Interface
        .cptra_ss_cptra_core_el2_mem_export(cptra_ss_cptra_core_el2_mem_export),
        .mldsa_memory_export_req(mldsa_memory_export.req),
    
    //SRAM interface for mbox
        .cptra_ss_cptra_core_mbox_sram_cs_o,
        .cptra_ss_cptra_core_mbox_sram_we_o,
        .cptra_sscptra_core_mbox_sram_addr_o,
        .cptra_ss_cptra_core_mbox_sram_wdata_o,
        .cptra_ss_cptra_core_mbox_sram_rdata_i,
    
    //SRAM interface for imem
        .cptra_ss_cptra_core_imem_cs_o,
        .cptra_ss_cptra_core_imem_addr_o,
        .cptra_ss_cptra_core_imem_rdata_i,

        .cptra_ss_cptra_core_bootfsm_bp_i,
       
    // TRNG Interface
    `ifdef CALIPTRA_INTERNAL_TRNG
        // External Request
        .cptra_ss_cptra_core_etrng_req_o,
        // Physical Source for Internal TRNG
        .cptra_ss_cptra_core_itrng_data_i,
        .cptra_ss_cptra_core_itrng_valid_i,
    `endif
    
    
    //MCU
        .cptra_ss_strap_mcu_lsu_axi_user_i,
        .cptra_ss_strap_mcu_ifu_axi_user_i,
        .cptra_ss_strap_mcu_sram_config_axi_user_i,
        .cptra_ss_strap_mci_soc_config_axi_user_i,

    //MCI
        .cptra_ss_mci_mcu_sram_req_if,
        .cptra_ss_mcu_mbox0_sram_req_if,
        .cptra_ss_mcu_mbox1_sram_req_if,
        .cptra_ss_mcu0_el2_mem_export,
        .cptra_ss_soc_mcu_mbox0_data_avail,
        .cptra_ss_soc_mcu_mbox1_data_avail,
        .cptra_ss_mci_boot_seq_brkpoint_i,
        .cptra_ss_mcu_no_rom_config_i,
        .cptra_ss_mci_generic_input_wires_i,
        .cptra_ss_strap_mcu_reset_vector_i,

        .cptra_ss_lc_Allow_RMA_or_SCRAP_on_PPD_i,
        .cptra_ss_FIPS_ZEROIZATION_PPD_i,

        .cptra_ss_mci_generic_output_wires_o,
        .cptra_ss_all_error_fatal_o,
        .cptra_ss_all_error_non_fatal_o,

        .cptra_ss_mcu_jtag_tck_i,
        .cptra_ss_mcu_jtag_tms_i,
        .cptra_ss_mcu_jtag_tdi_i,
        .cptra_ss_mcu_jtag_trst_n_i,
        .cptra_ss_mcu_jtag_tdo_o,
        .cptra_ss_mcu_jtag_tdoEn_o,

    //Strap
        .cptra_ss_strap_caliptra_base_addr_i,
        .cptra_ss_strap_mci_base_addr_i,
        .cptra_ss_strap_recovery_ifc_base_addr_i,
        .cptra_ss_strap_otp_fc_base_addr_i,
        .cptra_ss_strap_uds_seed_base_addr_i,
        .cptra_ss_strap_prod_debug_unlock_auth_pk_hash_reg_bank_offset_i,
        .cptra_ss_strap_num_of_prod_debug_unlock_auth_pk_hashes_i,
        .cptra_ss_strap_caliptra_dma_axi_user_i,
        .cptra_ss_strap_generic_0_i,
        .cptra_ss_strap_generic_1_i,
        .cptra_ss_strap_generic_2_i,
        .cptra_ss_strap_generic_3_i,
        .cptra_ss_debug_intent_i,
        .cptra_ss_dbg_manuf_enable_o,
        .cptra_ss_cptra_core_soc_prod_dbg_unlock_level_o,
    
        .cptra_ss_lc_clk_byp_ack_i           (cptra_ss_lc_clk_byp_ack_i),
        .cptra_ss_lc_clk_byp_req_o           (cptra_ss_lc_clk_byp_req_o),
        .cptra_ss_lc_ctrl_scan_rst_ni_i      (1'b1), // Note: Since we do not use dmi and use JTAG we do not need this
    
        .cptra_ss_lc_esclate_scrap_state0_i,
        .cptra_ss_lc_esclate_scrap_state1_i,
    
        .cptra_ss_soc_dft_en_o,
        .cptra_ss_soc_hw_debug_en_o,

        .cptra_ss_fuse_macro_outputs_i('0),
        .cptra_ss_fuse_macro_inputs_o,
    
    // I3C Interface
    `ifdef DIGITAL_IO_I3C
        .cptra_ss_i3c_scl_i(master0_intf.scl_and),
        .cptra_ss_i3c_sda_i(master0_intf.sda_and),
        .cptra_ss_i3c_scl_o(master0_intf.scl_and),
        .cptra_ss_i3c_sda_o(master0_intf.sda_and),
        .cptra_ss_sel_od_pp_o,
    `else
        .cptra_ss_i3c_scl_io,
        .cptra_ss_i3c_sda_io,
    `endif

        // -- remove in final version
        .cptra_ss_cptra_core_generic_input_wires_i,
        .cptra_ss_cptra_core_scan_mode_i,
        .cptra_error_fatal,
        .cptra_error_non_fatal,
        .ready_for_fuses,
        .ready_for_mb_processing,
        .mailbox_data_avail

    );
    



endmodule
