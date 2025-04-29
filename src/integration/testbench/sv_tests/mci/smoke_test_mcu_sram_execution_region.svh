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


task smoke_test_mcu_sram_execution_region();
    logic [31:0] rd_data;
    logic [31:0] rsp_user;
    axi_resp_e   resp;
    logic [$bits(m_axi_bfm_if.araddr)-1:0] write_addrs [9:0]; 
    logic [31:0] write_data [9:0]; 
    logic [31:0] axi_user;
    logic [31:0] fw_sram_exec_region_size;
    int         rand_choice;


    $display("[%t] Waiting for MCU to come out of reset", $time);
    wait_mcu_rst_b_deassert();
    @(posedge core_clk);
    $display("[%t] Bringing Caliptra out of reset", $time);
    bfm_axi_write_single_mcu_lsu(`SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, `MCI_REG_CPTRA_BOOT_GO_GO_MASK);

    // Randomize the size of the execution region:
    if($value$plusargs("SMOKE_TEST_MCU_SRAM_EXECUTION_REGION_MANUAL_FW_SRAM_EXEC_REGION_SIZE=%d", fw_sram_exec_region_size)) begin 
        $display("[%t] Setting FW_SRAM_EXEC_REGION_SIZE to: 0x%x", $time, fw_sram_exec_region_size);
        bfm_axi_write_single_mcu_lsu(`SOC_MCI_TOP_MCI_REG_FW_SRAM_EXEC_REGION_SIZE, fw_sram_exec_region_size); 
    end
    else begin
        $display("[%t] Setting random FW_SRAM_EXEC_REGION_SIZE", $time);
        set_random_fw_sram_exec_region_size();
    end
    
    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    
    //
    // Write last address in execution range
    //
    get_execution_last_dword_address(write_addrs[0]);
    write_data[0]  = $urandom;
    $display("[%t] Writing LAST address in Execution region 0x%x: 0x%x with AXI User: 0x%x", $time, write_addrs[0], write_data[0], axi_user);
    m_axi_bfm_if.axi_write_single(write_addrs[0],
                                  axi_user,
                                  ,   
                                  ,   
                                  write_data[0],
                                  axi_user,
                                  resp,
                                  rsp_user);
    if(resp !== AXI_RESP_OKAY) begin
        $error("Write response error: 0x%h when writing to 0x%h: 0x%h", resp, write_addrs[0], write_data[0]);
    end
    $display("[%t] Reading 0x%x", $time, write_addrs[0]);
    m_axi_bfm_if.axi_read_single(write_addrs[0],
                                  axi_user,
                                  ,
                                  ,
                                  rd_data,
                                  rsp_user,
                                  resp);
    $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[0], rd_data);
    if(resp !== AXI_RESP_OKAY) begin
        $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[0], rd_data);
    end
    if(rd_data !== write_data[0]) begin
        $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[0], write_data[0], rd_data);
    end



    //
    // 10 Random Writes and 10 reads to check the data written by Caliptrue
    //
    $display("[%t] 10 Random VALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        get_execution_rand_addr(write_addrs[i]);
        write_data[i]  = $urandom;
        $display("[%t] Writing 0x%x: 0x%x with AXI User: 0x%x", $time, write_addrs[i], write_data[i], axi_user);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Write response error: 0x%h when writing to 0x%h: 0x%h", resp, write_addrs[i], write_data[i]);
        end
    end

    $display("[%t] 10 Random VALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end
    
    // Disable assertion due to invalid accesses coming
    $assertoff(0, `MCI_PATH.i_mci_mcu_sram_ctrl.ERR_MCU_SRAM_EXEC_REGION_FILTER_ERROR);

    // 10 Reads to check data can't be accessed by invalid user
    $display("[%t] 10 Random INVALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        if(cptra_ss_strap_mcu_sram_config_axi_user_i !== cptra_ss_strap_caliptra_dma_axi_user_i) begin
            $display("[%t] Using CPTRA DMA user for invalid read", $time);
            axi_user = cptra_ss_strap_caliptra_dma_axi_user_i;
        end
        else begin
            $display("[%t] Using random user for invalid read", $time);
            axi_user = $urandom();
        end
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Reading 0x%x with AXI USER: 0x%h", $time, write_addrs[i], axi_user);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp === AXI_RESP_OKAY) begin
            $error("Read response needs to be an error: Response: 0x%x AXI USER 0x%h, Address 0x%x Valid user: 0x%x", resp, axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i);
        end
        if(rd_data !== '0) begin
            $error("Read data needs to be 0x0: AXI USER 0x%h, Address 0x%x Valid user: 0x%x Actual Data: 0x%x", axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i, rd_data);
        end
    end
    
    // 10 INVALID writes to already written MCU_SRAM
    $display("[%t] 10 Random INVALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        if(cptra_ss_strap_mcu_sram_config_axi_user_i !== cptra_ss_strap_caliptra_dma_axi_user_i) begin
            $display("[%t] Using CPTRA DMA user for invalid write", $time);
            axi_user = cptra_ss_strap_caliptra_dma_axi_user_i;
        end
        else begin
            $display("[%t] Using random user for invalid write", $time);
            axi_user = $urandom();
        end
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Writing 0x%x: 0x%x", $time, write_addrs[i], write_data[i]);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp === AXI_RESP_OKAY) begin
            $error("Write response needs to be an error: 0x%h when writing to 0x%h: 0x%h AXI USER: 0x%x" , resp, write_addrs[i], write_data[i], axi_user);
        end
    end
    
    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    $display("[%t] 10 Random VALID reads to MCU_SRAM to check INVALID writes", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

    $display("[%t] Setting fw_exec control to change access to MCU IFU and LSU", $time);
    force `CPTRA_SS_TOP_PATH.cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_i = 1'b1;

    rand_choice = $urandom_range(1,0);

    axi_user = rand_choice ? cptra_ss_strap_mcu_lsu_axi_user_i : cptra_ss_strap_mcu_ifu_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.

    $display("[%t] 10 Random VALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        get_execution_rand_addr(write_addrs[i]);
        write_data[i]  = $urandom;
        $display("[%t] Writing 0x%x: 0x%x with AXI User: 0x%x", $time, write_addrs[i], write_data[i], axi_user);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Write response error: 0x%h when writing to 0x%h: 0x%h", resp, write_addrs[i], write_data[i]);
        end
    end

    $display("[%t] 10 Random VALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end
    
    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    
    // 10 Reads to check data can't be accessed by invalid user
    $display("[%t] 10 Random INVALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Reading 0x%x with AXI USER: 0x%h", $time, write_addrs[i], axi_user);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp === AXI_RESP_OKAY) begin
            $error("Read response needs to be an error: Response: 0x%x AXI USER 0x%h, Address 0x%x Valid user: 0x%x", resp, axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i);
        end
        if(rd_data !== '0) begin
            $error("Read data needs to be 0x0: AXI USER 0x%h, Address 0x%x Valid user: 0x%x Actual Data: 0x%x", axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i, rd_data);
        end
    end
    
    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    
    // 10 INVALID writes to already written MCU_SRAM
    $display("[%t] 10 Random INVALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Writing 0x%x: 0x%x", $time, write_addrs[i], write_data[i]);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp === AXI_RESP_OKAY) begin
            $error("Write response needs to be an error: 0x%h when writing to 0x%h: 0x%h AXI USER: 0x%x" , resp, write_addrs[i], write_data[i], axi_user);
        end
    end
    
    axi_user = rand_choice ? cptra_ss_strap_mcu_lsu_axi_user_i : cptra_ss_strap_mcu_ifu_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    $display("[%t] 10 Random VALID reads to MCU_SRAM to check INVALID writes", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end
    
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
    $display("[%t] Clearing fw_exec control and MCU SRAM exec access protection should be identicle", $time);
    force `CPTRA_SS_TOP_PATH.cptra_ss_cptra_generic_fw_exec_ctrl_2_mcu_i = 1'b0;

    axi_user = rand_choice ? cptra_ss_strap_mcu_lsu_axi_user_i : cptra_ss_strap_mcu_ifu_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.

    $display("[%t] 10 Random VALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        get_execution_rand_addr(write_addrs[i]);
        write_data[i]  = $urandom;
        $display("[%t] Writing 0x%x: 0x%x with AXI User: 0x%x", $time, write_addrs[i], write_data[i], axi_user);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Write response error: 0x%h when writing to 0x%h: 0x%h", resp, write_addrs[i], write_data[i]);
        end
    end

    $display("[%t] 10 Random VALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end
    
    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    
    // 10 Reads to check data can't be accessed by invalid user
    $display("[%t] 10 Random INVALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Reading 0x%x with AXI USER: 0x%h", $time, write_addrs[i], axi_user);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp === AXI_RESP_OKAY) begin
            $error("Read response needs to be an error: Response: 0x%x AXI USER 0x%h, Address 0x%x Valid user: 0x%x", resp, axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i);
        end
        if(rd_data !== '0) begin
            $error("Read data needs to be 0x0: AXI USER 0x%h, Address 0x%x Valid user: 0x%x Actual Data: 0x%x", axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i, rd_data);
        end
    end
    
    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    
    // 10 INVALID writes to already written MCU_SRAM
    $display("[%t] 10 Random INVALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Writing 0x%x: 0x%x", $time, write_addrs[i], write_data[i]);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp === AXI_RESP_OKAY) begin
            $error("Write response needs to be an error: 0x%h when writing to 0x%h: 0x%h AXI USER: 0x%x" , resp, write_addrs[i], write_data[i], axi_user);
        end
    end
    
    axi_user = rand_choice ? cptra_ss_strap_mcu_lsu_axi_user_i : cptra_ss_strap_mcu_ifu_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    $display("[%t] 10 Random VALID reads to MCU_SRAM to check INVALID writes", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end

    
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
    $display("[%t] Setting MCU reset", $time);
    bfm_axi_write_single_mcu_lsu(`SOC_MCI_TOP_MCI_REG_RESET_REQUEST, `MCI_REG_RESET_REQUEST_MCU_REQ_MASK);
    wait_mcu_rst_b_assert();
    @(posedge core_clk);

    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    
    //
    // 10 Random Writes and 10 reads to check the data written by Caliptrue
    //
    $display("[%t] 10 Random VALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        get_execution_rand_addr(write_addrs[i]);
        write_data[i]  = $urandom;
        $display("[%t] Writing 0x%x: 0x%x with AXI User: 0x%x", $time, write_addrs[i], write_data[i], axi_user);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Write response error: 0x%h when writing to 0x%h: 0x%h", resp, write_addrs[i], write_data[i]);
        end
    end

    $display("[%t] 10 Random VALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end


    // 10 Reads to check data can't be accessed by invalid user
    $display("[%t] 10 Random INVALID reads to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        axi_user = $urandom();
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Reading 0x%x with AXI USER: 0x%h", $time, write_addrs[i], axi_user);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp === AXI_RESP_OKAY) begin
            $error("Read response needs to be an error: Response: 0x%x AXI USER 0x%h, Address 0x%x Valid user: 0x%x", resp, axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i);
        end
        if(rd_data !== '0) begin
            $error("Read data needs to be 0x0: AXI USER 0x%h, Address 0x%x Valid user: 0x%x Actual Data: 0x%x", axi_user, write_addrs[i], cptra_ss_strap_mcu_sram_config_axi_user_i, rd_data);
        end
    end
    
    // 10 INVALID writes to already written MCU_SRAM
    $display("[%t] 10 Random INVALID writes to MCU_SRAM", $time);
    for(int i = 0; i < 10; i++) begin
        axi_user = $urandom();
        @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
        $display("[%t] Writing 0x%x: 0x%x", $time, write_addrs[i], write_data[i]);
        m_axi_bfm_if.axi_write_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      write_data[i],
                                      axi_user,
                                      resp,
                                      rsp_user);
        if(resp === AXI_RESP_OKAY) begin
            $error("Write response needs to be an error: 0x%h when writing to 0x%h: 0x%h AXI USER: 0x%x" , resp, write_addrs[i], write_data[i], axi_user);
        end
    end
    
    axi_user = cptra_ss_strap_mcu_sram_config_axi_user_i;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.
    $display("[%t] 10 Random VALID reads to MCU_SRAM to check INVALID writes", $time);
    for(int i = 0; i < 10; i++) begin
        $display("[%t] Reading 0x%x", $time, write_addrs[i]);
        m_axi_bfm_if.axi_read_single(write_addrs[i],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        $display("[%t] Read 0x%x: 0x%x", $time, write_addrs[i], rd_data);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[i], rd_data);
        end
        if(rd_data !== write_data[i]) begin
            $error("Read data did not match expected address 0x%h: Expected 0x%x Actual 0x%x", write_addrs[i], write_data[i], rd_data);
        end
    end

    end_test_successful_req();


endtask
