
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
        $error("AXI WRITE: Write response error: 0x%h when writing to 0x%h: 0x%h with AXI USER:", resp, addr, data, user);
    end 
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


