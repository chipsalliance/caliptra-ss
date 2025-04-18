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
// Test Name: i3c_reg_rd_wr
// Description: This test is used to verify the I3C core register read and write functionality.
// It performs the following steps:
// 1. Wait for Dynamic Address Assignment and Bus Initialization
// 2. Grabs the dynamic address for the I3C core
// 3. Reads the Read Only Registers
// 4. Writes and Reads back the RECOVERY_CTRL Registers
// 5. Writes and Reads back the I3C_CORE_INDIRECT_FIFO_CTRL Registers
// 6. Writes and Reads back the I3C_CORE_INDIRECT_FIFO_DATA Registers

class i3c_setmrl extends cptra_ss_i3c_core_base_test;

	`avery_test_reg(i3c_setmrl)

	function new(string name, `avery_xvm_parent);
        super.new("i3c_setmrl", parent);
	endfunction

	virtual task read_reg(input ai3c_addr_t target_addr, input bit [7:0] addr, input int size, output bit [7:0] data[]);
		i3c_read(target_addr, addr, size, data);
		test_log.substep($psprintf("Received data:"));
		foreach(data[i]) begin
			test_log.substep($psprintf("data[%0d] = 'h %0h", i, data[i]));
		end
	endtask
	
	//-- test body
	virtual task test_body();

		bit [7:0] data[];
		bit [7:0] read_data[];
		int       random_data_count;

		//-- I3C bus initialization and address assignment
		i3c_bus_init();

		test_log.step("=============================================================");
		test_log.step("Step : Reading Recovery Register");
		read_reg(recovery_target_addr,`I3C_CORE_PROT_CAP, 15, read_data);

		test_log.step("Step : Writing General Target Address");
		// sending command as 0 for MCTP packet
		i3c_write(general_target_addr, data[0], data, data.size(), "MCTP");
		test_log.step("===============================================================");

		test_log.step("Step : Executing CCC SETMRL ");
		i3c_send_dc_ccc_setmrl();

		#100us;
		test_log.step("Step : ending test ... I3C SETMRL ");

	endtask

endclass