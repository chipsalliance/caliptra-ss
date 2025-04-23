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


task smoke_test_mcu_sram_debug_stress();
    logic [AXI_AW-1:0] write_addrs; 
    logic [AXI_AW-1:0] read_addrs; 
    logic [AXI_AW-1:0] mcu_sram_base_addr;
    logic [31:0]       read_data;
    int mcu_sram_size_dword;

    wait_debug_unlock();
    @(posedge core_clk);
    
    get_mcu_sram_size_byte(mcu_sram_size_dword);
    get_mcu_sram_base_addr(mcu_sram_base_addr);
    //
    // Write last address in execution range
    //
    for(int i = 0; i < mcu_sram_size_dword; i = i + 4) begin
        write_addrs = mcu_sram_base_addr + i; 
        if(!(i % 1000)) begin
            $display("[%t] Writing to address: 0x%x with 0x%x", $time, write_addrs, i);
        end
        bfm_axi_write_single_invalid_user(write_addrs, i);

    end

    for(int i = 0; i < mcu_sram_size_dword; i = i + 4) begin
        read_addrs = mcu_sram_base_addr + i; 
        bfm_axi_read_single_invalid_user( read_addrs,
                                         read_data); 

        if(!(i % 1000)) begin
            $display("[%t] Read data match at address: 0x%x, expected: 0x%x, got: 0x%x", $time, read_addrs, i, read_data);
        end
        if (read_data !== i) begin
            $error("[%t] ERROR: Read data mismatch at address: 0x%x, expected: 0x%x, got: 0x%x", $time, read_addrs, i, read_data);
        end
    end

    end_test_successful_req();


endtask
