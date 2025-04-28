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


task smoke_test_mci_axi_miss();
    logic [AXI_AW-1:0] addr;
    logic [31:0] data;

    wait_mcu_rst_b_deassert();

    for(int i= 0; i < 100; i++) begin
        get_mci_miss_address(addr);
        data = $urandom();
        $display("[%t] Checking invalid address 0x%h with the following data: 0x%h", $time, addr, data);
        bfm_axi_write_single_mcu_lsu(addr, data); 
        bfm_axi_read_single_mcu_lsu(addr, data);

        if (data !== '0) begin
            $error("[%t] ERROR: Read data was not 0. Address: 0x%h Actual Data: 0x%h", $time, addr, data);
        end
    end


    end_test_successful_req();

endtask
