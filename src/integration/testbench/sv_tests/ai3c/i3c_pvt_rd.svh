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
// -- Test Summary
// Test Name: i3c_pvt_rd
// Description: This test is used to verify the I3C core register read and write functionality.
// It performs the following steps:
// 1. Wait for Dynamic Address Assignment and Bus Initialization
// 2. Grabs the dynamic address for the I3C core
// 3. Reads the Read Only Registers
// 4. Writes and Reads back the RECOVERY_CTRL Registers
// 5. Writes and Reads back the I3C_CORE_INDIRECT_FIFO_CTRL Registers
// 6. Writes and Reads back the I3C_CORE_INDIRECT_FIFO_DATA Registers

class i3c_pvt_rd extends cptra_ss_i3c_core_base_test;
   
	`avery_test_reg(i3c_pvt_rd)

    localparam int MCTP_PKT_SIZE = 68;
   
    localparam int HEX_FILE_PER_LINE_BYTE = 16;
    localparam int HEX_FILE_LINE_NUM = 5;


	function new(string name, `avery_xvm_parent);
        super.new("i3c_pvt_rd", parent);
		err_count = 0;
	endfunction

	virtual task read_reg(input ai3c_addr_t target_addr, input bit [7:0] addr, input int size, output bit [7:0] data[]);
		i3c_read(target_addr, addr, size, data);
		test_log.substep($sformatf("Received data:"));
		foreach(data[i]) begin
			test_log.substep($sformatf("data[%0d] = 'h %0h", i, data[i]));
		end
	endtask

	//-- test body
	virtual task test_body();
	
		bit [7:0] read_data[];
		
		//-- I3C bus initialization and address assignment
		i3c_bus_init();

		for(int i = 0; i < 20; i++) begin
			test_log.step("Reading General Target Address");
			i3c_queue_read(general_target_addr, 7, read_data);
			test_log.substep($sformatf("General Target Address Read DATA: 'h %0h", read_data[0]));
			#1us;
		end

		test_log.step("=============================================================");
		test_log.step("I3C PVT Rd test completed");

	endtask

endclass