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

class i3c_reg_rd_wr extends cptra_ss_i3c_core_base_test;

	`avery_test_reg(i3c_reg_rd_wr)

	function new(string name, `avery_xvm_parent);
        super.new("i3c_reg_rd_wr", parent);
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
		test_log.step("Step : Reading Read Only Registers");

		read_reg(recovery_target_addr,`I3C_CORE_PROT_CAP, 15, read_data);
		read_reg(recovery_target_addr,`I3C_CORE_DEVICE_ID,  24, read_data);
		read_reg(recovery_target_addr,`I3C_CORE_DEVICE_STATUS,  7, read_data);
		read_reg(recovery_target_addr,`I3C_CORE_RECOVERY_STATUS,  2, read_data);
		read_reg(recovery_target_addr,`I3C_CORE_HW_STATUS,  4, read_data);
		read_reg(recovery_target_addr,`I3C_CORE_INDIRECT_FIFO_STATUS,  20, read_data);

		test_log.step("=============================================================");
		test_log.step("Step : Write & Read back RECOVERY_CTRL Registers");

		data = new[3];
		data[0] = 'h01;
		data[1] = 'h03;
		data[2] = 'h0f;
		
		test_log.substep($psprintf("Sending write to RECOVERY_CTRL register"));
		i3c_write(recovery_target_addr, `I3C_CORE_RECOVERY_CTRL, data, 3);

		test_log.substep($psprintf("Sending read to RECOVERY_CTRL register"));
		read_reg(recovery_target_addr,`I3C_CORE_RECOVERY_CTRL,  3, read_data);
		check_data(data, read_data, 3);
		
		test_log.step("=============================================================");
		test_log.step("Step : Write & Read back I3C_CORE_INDIRECT_FIFO_CTRL Registers");

		data = new[6];
		data[0] = 0;
		data[1] = 0;
		data[2] = 'h12;
		data[3] = 'h34;
		data[4] = 'h56;
		data[5] = 'h78;

		test_log.substep($psprintf("Sending write to INDIRECT_FIFO_CTRL register"));
		i3c_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_CTRL, data, 6);

		test_log.substep($psprintf("Sending read to INDIRECT_FIFO_CTRL register"));
		read_reg(recovery_target_addr,`I3C_CORE_INDIRECT_FIFO_CTRL,  6, read_data);		
		check_data(read_data, data, 6);

		//-- FIXME: https://github.com/chipsalliance/i3c-core/issues/36
		// test_log.step("=============================================================");
		// test_log.step("Step : Write & Read back I3C_CORE_INDIRECT_FIFO_DATA Registers");

		// random_data_count = $urandom_range(1, 20);
		// data = new[random_data_count];
		// foreach(data[i]) begin
		// 	data[i] = $urandom_range(0, 255);
		// end
			
		// test_log.substep($psprintf("Sending write to I3C_CORE_INDIRECT_FIFO_DATA register"));
		// i3c_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_DATA, data, random_data_count);

		// test_log.substep($psprintf("Sending read to I3C_CORE_INDIRECT_FIFO_DATA register"));
		// read_reg(recovery_target_addr,`I3C_CORE_INDIRECT_FIFO_DATA,  random_data_count, read_data);

		// check_data(read_data, data, random_data_count);

		test_log.step("=============================================================");
		test_log.step("I3C Reg Read & Write test completed");

	endtask

endclass