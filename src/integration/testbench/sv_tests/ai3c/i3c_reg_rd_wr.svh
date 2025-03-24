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
/*

*/

class i3c_reg_rd_wr extends cptra_ss_i3c_core_base_test;

	`avery_test_reg(i3c_reg_rd_wr)

	function new(string name, `avery_xvm_parent);
        super.new("i3c_reg_rd_wr", parent);
	endfunction

	virtual task read_reg(bit [7:0] addr, bit [7:0] data[], int size);
		i3c_read(target_addr, addr, size, data);
		test_log.substep($psprintf("Received data:"));
		foreach(data[i]) begin
			test_log.substep($psprintf("data[%0d] = 'h %0h", i, data[i]));
		end
	endtask

	//-- test body
	virtual task test_body();

		ai3c_addr_t general_target_addr;
		ai3c_addr_t recovery_target_addr;
		bit [7:0] data[];
		bit [7:0] read_data[];
		int       random_data_count;

		test_log.step("=================================================================");
		test_log.step("Wait for Dynamic Address Assignment and Bus Initialization");
		sys_agt.wait_event("bus_init_done", 1ms);
		test_log.step("Dynamic Address Assignment and Bus Initialization done");
		test_log.sample(AI3C_5_1_2_1n3);
		test_log.sample(AI3C_5_1_2_2n1);

		//-- grabbing dynamic address for the I3C core
		test_log.step($psprintf("I3C device count: %0d", sys_agt.mgr.dev_infos.size()));
		foreach (sys_agt.mgr.dev_infos[i]) begin
			case(sys_agt.mgr.dev_infos[i].sa)
				'h5A: begin
					general_target_addr= sys_agt.mgr.i3c_dev_das[i];
					test_log.substep($psprintf("I3C device 'd %0d: static addr 'h %0h, dynamic addr 'h %0h", i,sys_agt.mgr.dev_infos[i].sa, general_target_addr));
				end
				'h5B: begin
					recovery_target_addr = sys_agt.mgr.i3c_dev_das[i];
					test_log.substep($psprintf("I3C device 'd %0d: static addr 'h %0h, dynamic addr 'h %0h", i,sys_agt.mgr.dev_infos[i].sa, recovery_target_addr));
				end
				default: begin
					//-- print error message if the static address is not 0x5A or 0x5B
					test_log.substep($psprintf(" ERROR : I3C device %0d: static addr 'h %0h is not 0x5A or 0x5B", i, sys_agt.mgr.dev_infos[i].sa));
				end
			endcase
		end
		test_log.substep($psprintf("I3C Subordinate Recovery addr 'h %0h", recovery_target_addr));
		test_log.substep($psprintf("I3C Subordinate General addr 'h %0h", general_target_addr));

		test_log.step("=============================================================");
		test_log.step("Step : Reading Read Only Registers");

		read_reg(`I3C_CORE_PROT_CAP, read_data, 15);
		read_reg(`I3C_CORE_DEVICE_ID, read_data, 24);
		read_reg(`I3C_CORE_DEVICE_STATUS, daread_datata, 7);
		read_reg(`I3C_CORE_RECOVERY_STATUS, read_data, 2);
		read_reg(`I3C_CORE_HW_STATUS, read_data, 4);
		read_reg(`I3C_CORE_INDIRECT_FIFO_STATUS, read_data, 20);

		test_log.step("=============================================================");
		test_log.step("Step : Write & Read back RECOVERY_CTRL Registers");

		data = new[3];
		data[0] = 'h01;
		data[1] = 'h03;
		data[2] = 'h0f;
		
		test_log.substep($psprintf("Sending write to RECOVERY_CTRL register"));
		i3c_write(recovery_target_addr, `I3C_CORE_RECOVERY_CTRL, data, 3);

		test_log.substep($psprintf("Sending read to RECOVERY_CTRL register"));
		read_reg(`I3C_CORE_RECOVERY_CTRL, read_data, 3);
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
		read_reg(`I3C_CORE_INDIRECT_FIFO_CTRL, read_data, 6);
		check_data(data, read_data, 6);

		test_log.step("=============================================================");
		test_log.step("Step : Write & Read back I3C_CORE_INDIRECT_FIFO_DATA Registers");

		random_data_count = $urandom_range(1, 20);
		data = new[random_data_count];
		foreach(data[i]) begin
			data[i] = $urandom_range(0, 255);
		end
			
		test_log.substep($psprintf("Sending write to INDIRECT_FIFO_CTRL register"));
		i3c_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_DATA, data, random_data_count);

		test_log.substep($psprintf("Sending read to INDIRECT_FIFO_CTRL register"));
		read_reg(`I3C_CORE_INDIRECT_FIFO_DATA, read_data, random_data_count);
		check_data(data, read_data, random_data_count);

		test_log.step("=============================================================");
		test_log.step("I3C Reg Read & Write test completed");

	endtask

endclass