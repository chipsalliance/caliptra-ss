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
    localparam int NUM_BOUNDARY_DWORDS = 4;
    localparam int NUM_RANDOM_INTERIOR_ACCESSES = 200;
    localparam int NUM_ACCESSES = (2 * NUM_BOUNDARY_DWORDS) + NUM_RANDOM_INTERIOR_ACCESSES;

    logic [AXI_AW-1:0] access_addrs [NUM_ACCESSES-1:0];
    logic [AXI_AW-1:0] mcu_sram_base_addr;
    logic [AXI_AW-1:0] random_addr;
    logic [31:0]       write_data [NUM_ACCESSES-1:0];
    logic [31:0]       read_data;
    int                mcu_sram_size_bytes;
    logic              duplicate_addr;

    wait_debug_unlock();
    @(posedge core_clk);
    
    get_mcu_sram_size_byte(mcu_sram_size_bytes);
    get_mcu_sram_base_addr(mcu_sram_base_addr);

    if (mcu_sram_size_bytes < (NUM_ACCESSES * 4)) begin
        $fatal(1, "MCU SRAM is too small for %0d unique sampled accesses", NUM_ACCESSES);
    end

    for (int i = 0; i < NUM_BOUNDARY_DWORDS; i++) begin
        access_addrs[i] = mcu_sram_base_addr + (i * 4);
    end

    for (int i = 0; i < NUM_RANDOM_INTERIOR_ACCESSES; i++) begin
        do begin
            get_random_address_between(
                mcu_sram_base_addr + (NUM_BOUNDARY_DWORDS * 4),
                mcu_sram_base_addr + mcu_sram_size_bytes - ((NUM_BOUNDARY_DWORDS + 1) * 4),
                random_addr
            );
            duplicate_addr = 1'b0;
            for (int j = 0; j < NUM_BOUNDARY_DWORDS + i; j++) begin
                if (access_addrs[j] == random_addr) begin
                    duplicate_addr = 1'b1;
                end
            end
        end while (duplicate_addr);
        access_addrs[NUM_BOUNDARY_DWORDS + i] = random_addr;
    end

    for (int i = 0; i < NUM_BOUNDARY_DWORDS; i++) begin
        access_addrs[NUM_BOUNDARY_DWORDS + NUM_RANDOM_INTERIOR_ACCESSES + i] =
            mcu_sram_base_addr + mcu_sram_size_bytes - ((NUM_BOUNDARY_DWORDS - i) * 4);
    end

    $display("[%t] Testing %0d MCU SRAM locations: %0d boundary and %0d random interior accesses", $time, NUM_ACCESSES,
             2 * NUM_BOUNDARY_DWORDS, NUM_RANDOM_INTERIOR_ACCESSES);

    for (int i = 0; i < NUM_ACCESSES; i++) begin
        write_data[i] = access_addrs[i] - mcu_sram_base_addr;
        bfm_axi_write_single_invalid_user(access_addrs[i], write_data[i]);
        if (!(i % 50)) begin
            $display("[%t] Wrote sample %0d/%0d at address 0x%x", $time, i + 1, NUM_ACCESSES, access_addrs[i]);
        end
    end

    for (int i = 0; i < NUM_ACCESSES; i++) begin
        bfm_axi_read_single_invalid_user(access_addrs[i], read_data);
        if (!(i % 50)) begin
            $display("[%t] Read sample %0d/%0d at address 0x%x", $time, i + 1, NUM_ACCESSES, access_addrs[i]);
        end
        if (read_data !== write_data[i]) begin
            $error("[%t] ERROR: Read data mismatch at address: 0x%x, expected: 0x%x, got: 0x%x", $time, access_addrs[i], write_data[i], read_data);
        end
    end

    end_test_successful_req();
endtask
