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


task mcu_mbox_soc_agent_write_fw_image();
    localparam FW_BLOB_SIZE_BYTES = 200;
    localparam FW_BLOB_SIZE_DWORDS = FW_BLOB_SIZE_BYTES/4;

    localparam MCU_MBOX_CMD_COMPLETE = 2;
    localparam WAIT_ATTEMPT_TIMEOUT_LIMIT = 2147483646;

    logic [31:0] rd_data;
    logic [31:0] rsp_user;
    axi_resp_e   resp;
    logic [$bits(m_axi_bfm_if.araddr)-1:0] write_addrs [9:0]; 
    logic [31:0] write_data [9:0]; 
    logic [31:0] axi_user;
    logic [31:0] wuser_array [];
    logic [3:0]  wstrb_array[];
    logic [7:0] data_array[FW_BLOB_SIZE_BYTES-1:0];
    logic [31:0] fw_blob [FW_BLOB_SIZE_DWORDS-1:0];

    int hex_file_is_empty;
    int mbox_num = 0;

    $display("[%t] Waiting for MCU to come out of reset", $time);
    wait_mcu_rst_b_deassert();
    @(posedge core_clk);

    axi_user = 32'h12345678;
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.

    // Wait for CLPTRA_BOOT_GO to be set
    get_cptra_boot_go_address(write_addrs[0]);
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.

    $display("[%t] ait for CLPTRA_BOOT_GO to be set", $time);
    for(int i = 0; i < 100000; i++) begin
        m_axi_bfm_if.axi_read_single(write_addrs[0],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[0], rd_data);
        end
        if (rd_data != 0) begin
            $display("[%t] ait for CLPTRA_BOOT_GO to be set: 0x%x", $time, rd_data);
            break;
        end
    end
        

    // Wait for MCU to configure valid axi user
    get_mcu_mbox_valid_axi_user_address(write_addrs[0]);
    @(posedge core_clk); // Delay to avoid race condition with the AXI BFM.

    $display("[%t] Waiting for MCU to add SoC agent to valid AXI user", $time);
    for(int i = 0; i < 100000; i++) begin
        m_axi_bfm_if.axi_read_single(write_addrs[0],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[0], rd_data);
        end
        if (rd_data == axi_user) begin
            $display("[%t] Mbox User AXI: 0x%x", $time, rd_data);
            break;
        end
    end
    $display("[%t] Mbox User AXI Updated: 0x%x", $time, rd_data);

    get_mcu_mbox_axi_user_lock_address(write_addrs[0]);
    for(int i = 0; i < WAIT_ATTEMPT_TIMEOUT_LIMIT; i++) begin

        m_axi_bfm_if.axi_read_single(write_addrs[0],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[0], rd_data);
        end
        if (rd_data == 1) begin
            $display("[%t] Mbox User AXI Locked: 0x%x", $time, rd_data);
            break;
        end
        if (i == WAIT_ATTEMPT_TIMEOUT_LIMIT-1) begin
            $error("[%t] ERROR: Mbox User AXI Lock not set: 0x%x", $time, rd_data);
        end
    end

    get_mcu_mbox_lock_address(write_addrs[0]);
    @(posedge core_clk); 

    $display("[%t] Waiting for MCU to clear the mbox lock out of reset and SoC agent to acquire lock", $time);
    for(int i = 0; i < WAIT_ATTEMPT_TIMEOUT_LIMIT-1; i++) begin

        m_axi_bfm_if.axi_read_single(write_addrs[0],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[0], rd_data);
        end
        if (rd_data == 0) begin
        $display("[%t] Mbox Lock Read: 0x%x", $time, rd_data);
            break;
        end
        if (i == WAIT_ATTEMPT_TIMEOUT_LIMIT-1) begin
            $error("[%t] ERROR: Mbox Lock not cleared: 0x%x", $time, rd_data);
        end
    end
    $display("[%t] MCU Mbox Lock Cleared and Acquired by SoC Agent", $time);

    // Reading side hex file for hitless
    hex_file_is_empty = $system("test -s mcu_hitless_lmem.hex");
    $display("[%t] MCU Mbox Hex Empty: %d", $time, hex_file_is_empty);
    if (!hex_file_is_empty) $readmemh("mcu_hitless_lmem.hex", data_array);

    for(int i = 0; i < FW_BLOB_SIZE_DWORDS; i++) begin
        fw_blob[i] = {data_array[i*4+3], data_array[i*4+2], data_array[i*4+1], data_array[i*4]};
    end

    //for(int i = 0; i < 100; i++) begin
    //    $display("[%t] SRAM dword[%d]: 0x%x", $time, i, fw_blob[i]);
    //end

    // Writing side hex image for hitless to Mbox SRAM
    $display("[%t] Writing hitless FW image to MCU Mbox SRAM", $time);

    for(int i = 0; i < FW_BLOB_SIZE_DWORDS; i++) begin
        get_mcu_mbox_sram_addr(write_addrs[0], i, mbox_num);
        @(posedge core_clk); 
        m_axi_bfm_if.axi_write_single(write_addrs[0],
                                        axi_user,
                                        ,   
                                        ,   
                                        fw_blob[i],
                                        axi_user,
                                        resp,
                                        rsp_user);
        $display("[%t] Writing to 0x%h: 0x%h", $time, write_addrs[0], fw_blob[i]);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Write response error: 0x%h when writing to 0x%h: 0x%h", resp, write_addrs[0], {data_array[i*4+3], data_array[i*4+2], data_array[i*4+1], data_array[i*4]});
        end
    end

    $display("[%t] Hitless FW image written to MCU Mbox SRAM", $time);


    //wstrb_array = new[FW_BLOB_SIZE_DWORDS]('{default: {4{1'b1}}});
    //get_mcu_mbox_sram_addr(write_addrs[0], 0, mbox_num);
    //@(posedge core_clk); 
    //m_axi_bfm_if.axi_write(.addr(write_addrs[0]),
    //                        .len(FW_BLOB_SIZE_DWORDS-1),
    //                        .user(axi_user),
    //                        .data(fw_blob),
    //                        .strb(wstrb_array),
    //                        .use_strb(0),
    //                        .use_write_user(0),
    //                        .write_user(wuser_array),  
    //                        .resp(resp),
    //                        .resp_user(rsp_user));
    
    // Write dlen
    get_mcu_mbox_dlen_addr(write_addrs[0], mbox_num);
    @(posedge core_clk); 

    write_data[0] = FW_BLOB_SIZE_DWORDS*4;

    $display("[%t] Hitless FW image DLEN: 0x%x", $time, write_data[0]);
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

    // Write cmd
    $display("[%t] Hitless FW image set command", $time);

    get_mcu_mbox_cmd_addr(write_addrs[0], mbox_num);
    @(posedge core_clk); 

    write_data[0] = 32'habcd;

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

    // Set execute
    $display("[%t] Hitless FW image set execute", $time);

    get_mbox_mcu_execute_addr(write_addrs[0], mbox_num);
    @(posedge core_clk); 

    write_data[0] = 1;

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

    // Wait for MCU to set complete once Caliptra is done with image
    $display("[%t] Waiting for MCU to set complete in mailbox once Caliptra is done", $time);

    get_mbox_mcu_cmd_status_addr(write_addrs[0], mbox_num);
    @(posedge core_clk); 

    for(int i = 0; i < WAIT_ATTEMPT_TIMEOUT_LIMIT; i++) begin
        m_axi_bfm_if.axi_read_single(write_addrs[0],
                                      axi_user,
                                      ,
                                      ,
                                      rd_data,
                                      rsp_user,
                                      resp);
        if(resp !== AXI_RESP_OKAY) begin
            $error("Read response error: 0x%h when reading to 0x%h: 0x%h", resp, write_addrs[0], rd_data);
        end
        if (rd_data == MCU_MBOX_CMD_COMPLETE) begin
        $display("[%t] Mbox Cmd Complete Set: 0x%x", $time, rd_data);
            break;
        end
        if(i == WAIT_ATTEMPT_TIMEOUT_LIMIT-1) begin
            $error("[%t] ERROR: Mbox Cmd Complete not set: 0x%x", $time, rd_data);
        end
    end

endtask
