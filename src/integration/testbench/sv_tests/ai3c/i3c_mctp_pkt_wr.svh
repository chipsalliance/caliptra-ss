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
// Test Name: i3c_mctp_pkt_wr
// Description: This test is used to verify the I3C core register read and write functionality.
// It performs the following steps:
// 1. Wait for Dynamic Address Assignment and Bus Initialization
// 2. Grabs the dynamic address for the I3C core
// 3. Reads the Read Only Registers
// 4. Writes and Reads back the RECOVERY_CTRL Registers
// 5. Writes and Reads back the I3C_CORE_INDIRECT_FIFO_CTRL Registers
// 6. Writes and Reads back the I3C_CORE_INDIRECT_FIFO_DATA Registers

class i3c_mctp_pkt_wr extends cptra_ss_i3c_core_base_test;
   
	`avery_test_reg(i3c_mctp_pkt_wr)

    localparam int MCTP_PKT_SIZE = 68;
   
    localparam int HEX_FILE_PER_LINE_BYTE = 16;
    localparam int HEX_FILE_LINE_NUM = 5;


	function new(string name, `avery_xvm_parent);
        super.new("i3c_mctp_pkt_wr", parent);
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

		bit [7:0] data[];
		bit [7:0] read_data[];
		int       random_data_count;
		bit [7:0] mctp_data[25][16];
		int       num_of_mctp_pkt;
		string filename = "mctp_pkt.hex";
    	integer file;
		int     i3c_data_idx;
		string line;
		
		//-- I3C bus initialization and address assignment
		i3c_bus_init();

		test_log.step("=============================================================");
		test_log.step("Step : Writing General Target Interface with Random Data");

		//-- randomize number of mctp packets from 1 to 10
		if($value$plusargs("num_of_mctp_pkt=%0d",num_of_mctp_pkt)) begin
			test_log.substep($sformatf("Number of MCTP packets to be sent: %0d", num_of_mctp_pkt));
		end else begin
			num_of_mctp_pkt = $urandom_range(1,5);
		end

		//-- if file mctp_pkt.hex exists, read mctp_data from the file
		//-- if file does not exist, generate random mctp_data

		file = $fopen(filename, "r"); // Open the file in read mode
		if (file) begin
			test_log.step("Reading mctp_data from file mctp_pkt.hex");
			$readmemh("mctp_pkt.hex", mctp_data);
			$fclose(file); // Close the file
		end else begin
			test_log.step("Generating random mctp_data");
			foreach(mctp_data[i]) begin
				foreach(mctp_data[i][j]) begin
					//-- randomize mctp_data[i][j] from 0 to 255
					mctp_data[i][j] = $urandom_range(0, 255);
				end
			end
		end
		test_log.substep($sformatf("mctp_data:"));
		foreach(mctp_data[i]) begin
			line ="";
			foreach(mctp_data[i][j]) begin
				line = $sformatf("%s %0x", line, mctp_data[i][j]);
			end
			test_log.substep($sformatf("mctp_data[%0d] = 'h %s", i, line));
		end
	

		test_log.step("=============================================================");
		test_log.step("Step : Writing General Target Interface with Random Data");

		for (int pkt_num=0; pkt_num<num_of_mctp_pkt; pkt_num++) begin

			test_log.substep($sformatf("Writing MCTP packet %0d", pkt_num));

			//-- reading 68 bytes from the mctp_data array
			data = new[MCTP_PKT_SIZE];
            for(int i=0; i<HEX_FILE_LINE_NUM; i++) begin				
                for(int j=0; j<HEX_FILE_PER_LINE_BYTE; j++) begin
                    data[i*HEX_FILE_PER_LINE_BYTE+j] = mctp_data[pkt_num*HEX_FILE_LINE_NUM+i][j];
                    if(i==HEX_FILE_LINE_NUM-1 && j==3) begin
                        break;
                    end
                end
			end

			// sending command as 0 for MCTP packet
			i3c_write(general_target_addr, data[0], data, data.size(), "MCTP");

            test_log.step("Waiting for 100us before sending next packet");
            #100us;
		end

        test_log.step("Waiting for 100us to allow mcu to read the packet");
        #100us;

		test_log.step("=============================================================");
		test_log.step("I3C MCTP Packet Write completed");

	endtask

endclass