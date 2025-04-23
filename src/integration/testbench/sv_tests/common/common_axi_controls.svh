
class RandInvalidAXIUser;
  randc logic [31:0] rand_user;
  logic [31:0] strap_mcu_lsu_axi_user;
  logic [31:0] strap_mcu_ifu_axi_user;
  logic [31:0] strap_mcu_sram_config_axi_user;
  logic [31:0] strap_mci_soc_config_axi_user;

  constraint c_avoid_values {
    rand_user != strap_mcu_lsu_axi_user;
    rand_user != strap_mcu_ifu_axi_user;
    rand_user != strap_mcu_sram_config_axi_user;
    rand_user != strap_mci_soc_config_axi_user;
  }
  function new(
    logic [31:0] i_strap_mcu_lsu_axi_user,
    logic [31:0] i_strap_mcu_ifu_axi_user,
    logic [31:0] i_strap_mcu_sram_config_axi_user,
    logic [31:0] i_strap_mci_soc_config_axi_user);
    strap_mcu_lsu_axi_user = i_strap_mcu_lsu_axi_user;
    strap_mcu_ifu_axi_user = i_strap_mcu_ifu_axi_user;
    strap_mcu_sram_config_axi_user = i_strap_mcu_sram_config_axi_user;
    strap_mci_soc_config_axi_user = i_strap_mci_soc_config_axi_user;
  endfunction


endclass


task bfm_axi_read_single(input [AXI_AW-1:0] addr,
                          input [31:0]       user,
                          output [31:0]      data);
    axi_resp_e   resp;
    logic [31:0] rsp_user;

    m_axi_bfm_if.axi_read_single(addr,
                                  user,
                                  ,
                                  ,
                                  data,
                                  rsp_user,
                                  resp);
    if(resp !== AXI_RESP_OKAY) begin
        $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, addr, data);
    end
endtask

task automatic bfm_axi_read_single_invalid_user( input [AXI_AW-1:0] addr,
                                                 output [31:0]       data); 
    RandInvalidAXIUser invalid_axi_user_gen = new(
        cptra_ss_strap_mcu_lsu_axi_user_i,
        cptra_ss_strap_mcu_ifu_axi_user_i,
        cptra_ss_strap_mcu_sram_config_axi_user_i,
        cptra_ss_strap_mci_soc_config_axi_user_i
    );
    
    if (!invalid_axi_user_gen.randomize()) begin
        $fatal("Randomization failed!");
    end
    bfm_axi_read_single(addr, invalid_axi_user_gen.rand_user, data);
endtask

task bfm_axi_write_single(input [AXI_AW-1:0] addr,
                          input [31:0]       user,
                          input [31:0]       data); 
    axi_resp_e   resp;
    logic [31:0] rsp_user;
    m_axi_bfm_if.axi_write_single(addr,
                                  user,
                                  ,   
                                  ,   
                                  data,
                                  user,
                                  resp,
                                  rsp_user);
    if(resp !== AXI_RESP_OKAY) begin
        $error("AXI WRITE: Write response error: 0x%h when writing to 0x%h: 0x%h with AXI USER: 0x%h", resp, addr, data, user);
    end 
endtask

task automatic bfm_axi_write_single_invalid_user(input [AXI_AW-1:0] addr,
                                                 input [31:0]       data); 
    RandInvalidAXIUser invalid_axi_user_gen = new(
        cptra_ss_strap_mcu_lsu_axi_user_i,
        cptra_ss_strap_mcu_ifu_axi_user_i,
        cptra_ss_strap_mcu_sram_config_axi_user_i,
        cptra_ss_strap_mci_soc_config_axi_user_i
    );
    
    if (!invalid_axi_user_gen.randomize()) begin
        $fatal("Randomization failed!");
    end
    bfm_axi_write_single(addr, invalid_axi_user_gen.rand_user, data);
endtask

task bfm_axi_write_single_mcu_lsu(input [AXI_AW-1:0] addr,
                                  input [31:0]       data); 
    bfm_axi_write_single(addr, cptra_ss_strap_mcu_lsu_axi_user_i, data);
endtask

task bfm_axi_write_single_mcu_ifu(input [AXI_AW-1:0] addr,
                                  input [31:0]       data); 
    bfm_axi_write_single(addr, cptra_ss_strap_mcu_ifu_axi_user_i, data);
endtask

task bfm_axi_write_single_caliptra_dma(input [AXI_AW-1:0] addr,
                                  input [31:0]       data); 
    bfm_axi_write_single(addr, cptra_ss_strap_caliptra_dma_axi_user_i, data);
endtask

task bfm_axi_write_single_mcu_sram_config(input [AXI_AW-1:0] addr,
                                  input [31:0]       data); 
    bfm_axi_write_single(addr, cptra_ss_strap_mcu_sram_config_axi_user_i, data);
endtask


