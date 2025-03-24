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
 * I3C Random Streaming Boot Test
 * Randomizes
 * 	- Image Size
 *  - I3C Image write Size
*/

class i3c_rand_streaming_boot extends cptra_ss_i3c_core_base_test;

	`avery_test_reg(i3c_rand_streaming_boot)

	function new(string name, `avery_xvm_parent);
        super.new("i3c_rand_streaming_boot", parent);
	endfunction

	virtual task test_body();

		ai3c_addr_t general_target_addr;
		ai3c_addr_t recovery_target_addr;
		ai3c_addr_t addr = 8'h5A;
		bit ok;
		bit [7:0] data[];
		bit [7:0] exp_data[];

		int fp;
		string line;
		int i = 0;
		bit [7:0] read_mem[8192][16];
		bit [7:0] image[][];
		bit [31:0] img_sz;
		int img_sz_in_16B;
		int img_sz_in_4B;
		int wr_count_256B;
		int wr_count_16B;
		int wr_count_4B;
		int wr_count_1B;
		int r;
		bit [31:0] cmdline_img_sz;
		bit [31:0] remaining_img_sz_in_bytes;

		test_log.step("=================================================================");
		test_log.step("Step 0: Reading Firmware test image from file");

		// -- firmware image size
		// -- check if,
		// -- 1. cmdline argument is provided
		// -- 2. random image size is provided
		// -- if not, read the image size from the file
		if($value$plusargs("cmdline_img_sz=%h", cmdline_img_sz)) begin
			
			test_log.substep($psprintf("using CMD Line for Image Size (in bytes): 'd %0d",cmdline_img_sz));
			img_sz = cmdline_img_sz;
		
		end else if ($test$plusargs("random_img_sz")) begin

			test_log.substep($psprintf("using random image size"));
			img_sz = 4 + ($urandom_range(0, 319) * 4); //-- 4 to 1280 bytes
			test_log.substep($psprintf("Random Image Size (in bytes): 'd %0d",img_sz));

		end else begin

			test_log.substep($psprintf("using file ./fw_update.size for Image size"));
			// Check if file exists and read size
			fp = $fopen("./fw_update.size", "r");
			if (fp == 0) begin
				test_log.step($psprintf("ERROR : File not found: %s", "./fw_update.size"));
			end
			r = $fgets(line, fp);
			if (r == 0) begin
				test_log.step($psprintf("ERROR : File read error: %s", "./fw_update.size"));
			end
			img_sz = line.atoi();
			$fclose(fp);

		end

		if (img_sz > 0) begin
			test_log.substep($psprintf("Image Size (in bytes): 'd %0d",img_sz));
		end else begin
			test_log.step($psprintf("ERROR : Invalid image size: 'd %0d", img_sz));
		end
		
		// -- for aligned image size
		wr_count_256B =  (img_sz)     / 256;
		wr_count_16B  =  (img_sz%256) /16;
		wr_count_4B   =  (img_sz%16)  /4;
		wr_count_1B   =  (img_sz%4);
		
		if(wr_count_1B > 0) begin
			test_log.substep($psprintf("Error : Image size is not multiples of 4 Bytes"));
		end

		test_log.substep($psprintf("== Img Wr Count for 256B : 'd %0d x 256 B = 'd %0d B", wr_count_256B, (wr_count_256B*256)));
		test_log.substep($psprintf("== Img Wr Count for  16B : 'd %0d x  16 B = 'd %0d B", wr_count_16B, (wr_count_16B*16)));
		test_log.substep($psprintf("== Img Wr Count for  4B  : 'd %0d x   4 B = 'd %0d B", wr_count_4B, (wr_count_4B*4)));
		test_log.substep($psprintf("== Calculated Image Size ==  'd %0d B", ((wr_count_256B*256)+(wr_count_16B*16)+(wr_count_4B*4))));

		//-- for unaligned image size
		img_sz_in_16B = img_sz/16 + (img_sz%16 > 0? 1 : 0);
		test_log.substep($psprintf("Image Size (in 16B): 'd %0d",img_sz_in_16B));

		//-- for unaligned image size
		img_sz_in_4B = img_sz/4;
		test_log.substep($psprintf("Image Size (in 4B): 'h %0h ",img_sz_in_4B));
		

		// renew image array
		image = new[img_sz_in_16B];
		for(int i = 0; i < img_sz_in_16B; i++) begin
			image[i] = new[16];
		end

		$readmemh("fw_update.hex", read_mem);
		if ($isunknown(read_mem[0][0])) begin
			test_log.step($psprintf("ERROR : File read error: %s", "fw_update.hex"));
		end
		//-- writing image to array
		foreach(image[i]) begin
			line = "'h ";
			for(int j = 0; j < 16; j++) begin
				image[i][j] = read_mem[i][j];
				line = $psprintf("%s %0h", line, image[i][j]);
			end
			test_log.substep($psprintf("Image['d %0d]: %0s", i, line));
		end
			
		test_log.substep("Reading Firmware test image from file completed.");

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
		test_log.step("Step 1: Reading Base Registers");

		test_log.substep("Reading PROT_CAP register");
		
		exp_data = new[15];
		exp_data = '{'h20, 'h50, 'h43, 'h4f, 'h56, 'h43, 'h45, 'h52, 'h00, 'h00, 'h00, 'h00, 'h00, 'h00, 'h00};
		exp_data[10] |= 1 << 7;
		exp_data[11] |= 1 << (10 - 8);
		exp_data[11] |= 1 << (11 - 8);
		i3c_read(recovery_target_addr, `I3C_CORE_PROT_CAP, 15, data);
		check_data(data, exp_data, 15);

		test_log.substep("Reading DEVICE_ID register");
		i3c_read(recovery_target_addr, `I3C_CORE_DEVICE_ID, 24, data);
	
        test_log.substep("Reading HW_STATUS register");
		i3c_read(recovery_target_addr, `I3C_CORE_HW_STATUS, 4, data);

		test_log.substep("Reading DEVICE_STATUS register");
		i3c_read(recovery_target_addr, `I3C_CORE_DEVICE_STATUS, 4, data);

		test_log.step("=============================================================");
		test_log.step("Step 2: waiting for recovery start");

		//-- reading device status
		//-- DEVICE_STATUS ('d36)
		data = new[8];
		data[0] = 0;
		test_log.substep($psprintf("Reading DEVICE_STATUS register"));
		for(int i = 0; i < 1; i++) begin //-- FIXME : should be 100
			i3c_read(recovery_target_addr, `I3C_CORE_DEVICE_STATUS, 8, data);
			if(data[0] == 'h3) begin
				test_log.substep($psprintf("Recovery started : 'd %0d", data[0]));
				break;
			end
			#1us;
		end
		if(data[0] != 'h3) begin	
			test_log.substep("Recovery did not start"); //-- FIXME : it must be an error
		end

		//-- Reading RECOVERY_STATUS register for recovery status
		//-- RECOVERY_STATUS ('d39)
		test_log.substep($psprintf("Reading RECOVERY_STATUS register"));
		for(int i = 0; i < 100; i++) begin
			i3c_read(recovery_target_addr, `I3C_CORE_RECOVERY_STATUS, 2, data);
			if(data[0] == 'h1) begin
				test_log.substep($psprintf("Device recovery status : 0x1: Awaiting recovery image"));
				break;
			end
			#1us;
		end
		if(data[0] != 'h1) begin
			test_log.substep("Recovery did not start");
		end

		test_log.step("=============================================================");
		test_log.step("Step 3: Writing Recovery Image");
		//-- writing RECOVERY_CTRL register
		//-- RECOVERY_CTRL ('d38)
		data = new[3];
		data[0] = 'h0; // Component Memory Space (CMS)
		data[1] = 'h0; // Use Recovery Image from memory window (CMS)
		data[2] = 'h0; // do not activate recovery image
		test_log.substep($psprintf("Sending write to RECOVERY_CTRL register"));
		i3c_write(recovery_target_addr, `I3C_CORE_RECOVERY_CTRL, data, 'h3);

		//-- writing INDIRECT_FIFO_CTRL register
		//-- INDIRECT_FIFO_CTRL ('d45)
		//-- Step 7:
		//-- BMC or a similar platform component will update INDIRECT_FIFO_CTRL 
		//-- with Component Memory Space (CMS) byte 0 with 0x0, 
		//-- Reset field byte 1 with 0x1 and 
		//-- Image size byte 2 to 5 field to size of the image.
		data = new[6];
		data[0] = 'h0; // CMS set to 0
		data[1] = 'h0; // FIXME : reset the FIFO by writing 1 

		data[2] = img_sz_in_4B[7:0]; // Image size 0
		data[3] = img_sz_in_4B[15:8]; // Image size 1
		data[4] = img_sz_in_4B[23:16];  // Image size 2
		data[5] = img_sz_in_4B[31:24];  // Image size 3

		
		
		test_log.substep($psprintf("Sending write to INDIRECT_FIFO_CTRL register"));
		i3c_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_CTRL, data, 6);

		//-- writing INDIRECT_FIFO_DATA register
		//-- Step 8:
		//-- BMC or a similar platform component writes to INDIRECT_FIFO_DATA register. 
		//-- I3C device shall return a NACK response for any transfer that would cause 
		//-- the Head Pointer to advance to equal the Tail Pointer. 
		//-- BMC can implement flow control through NACK responses. 
		
		remaining_img_sz_in_bytes = img_sz;

		while(remaining_img_sz_in_bytes > 0) begin
		
			test_log.substep($psprintf("Writing 'd %0d of 256B blocks", wr_count_256B));
			if(remaining_img_sz_in_bytes > 256) begin
				test_log.substep($psprintf("Writing 'd %0d of 256B blocks", wr_count_256B));
				for(int i = 0; i < wr_count_256B; i++) begin

					test_log.step($psprintf("INDIRECT_FIFO_DATA write..'d %0d", i));
					data = new[256];
					line = "'h ";
					for (int k = 0; k < 256; k++) begin
						for(int j = 0; j < 16; j++) begin
							data[k] = image[i*16+k][j];
							line = $psprintf("%s%0h", line, data[k]);
						end
						test_log.substep($psprintf("Image['d %0d]: %s", (i*16+k), line));
					end
					test_log.substep($psprintf("Sending write to INDIRECT_FIFO_DATA register"));
					i3c_random_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_DATA, data, 256);
					remaining_img_sz_in_bytes = remaining_img_sz_in_bytes - 256;

					if (remaining_img_sz_in_bytes > 0) begin
						test_log.substep($psprintf("Remaining Image Size (in bytes): 'd %0d", remaining_img_sz_in_bytes));
						//-- read INDIRECT_FIFO_STATUS register
						//-- INDIRECT_FIFO_STATUS ('d46)
						//-- Step 9:
						//-- The I3C device will keep head and tail pointers along with 
						//-- FIFO status up to date into INDIRECT_FIFO_STATUS register. 
						//-- I3C recovery interface HW wait for an update to 
						//-- INDIRECT_DATA_REG with 1-256B data from BMC.
						data[0] = 0;
						for(int i = 0; i < 100; i++) begin
							i3c_read(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_STATUS, 20, data);
							if(data[0] == 'h1) begin
								test_log.substep("Indirect FIFO is empty");
								break;
							end
							#100ns;
						end
						if(data[0] != 'h1) begin
							test_log.substep("Indirect FIFO is not empty after 100 read attempts.. TIMEOUT");
						end
					end else begin
						test_log.substep($psprintf("Image send completed"));
					end

				end
			end else begin
				test_log.substep($psprintf("writing remaining image size 'd %0d", remaining_img_sz_in_bytes));
				data = new[remaining_img_sz_in_bytes];
				line = "'h ";
				for (int k = 0; k < remaining_img_sz_in_bytes; k++) begin
					for(int j = 0; j < 16; j++) begin
						data[k] = image[(wr_count_256B*16)+k][j];
						line = $psprintf("%s%0h", line, data[k]);
					end
					test_log.substep($psprintf("Image['d %0d]: %s", ((wr_count_256B*16)+k), line));
				end
				test_log.substep($psprintf("Sending write to INDIRECT_FIFO_DATA register"));
				i3c_random_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_DATA, data, remaining_img_sz_in_bytes);
				remaining_img_sz_in_bytes = remaining_img_sz_in_bytes - remaining_img_sz_in_bytes;
			end
			test_log.substep($psprintf("Remaining Image Size (in bytes): 'd %0d / 'd %0d", remaining_img_sz_in_bytes, img_sz));

		end

		test_log.step("=============================================================");
		test_log.step("Step 4: Recovery Image Activation");

		//-- writing RECOVERY_CTRL register
		//-- RECOVERY_CTRL ('d38)
		//-- step 12 & 13: 
		//-- BMC or a similar platform component will update RECOVERY_CTRL
		//-- with Component Memory Space (CMS) byte 0 with 0x0,
		//-- Use Recovery Image from memory window (CMS) byte 1 with 0x0 and
		//-- activate recovery image byte 2 with 0x1.

		data = new[3];
		data[0] = 'h00; // Component Memory Space (CMS)
		data[1] = 'h00; // Use Recovery Image from memory window (CMS)
		data[2] = 'h0F; // activate recovery image
		test_log.substep($psprintf("Sending write to RECOVERY_CTRL register"));
		i3c_write(recovery_target_addr, `I3C_CORE_RECOVERY_CTRL, data, 'h3	);

		//-- reading RECOVERY_STATUS register
		//-- RECOVERY_STATUS ('d39)
		//-- Step 14:
		//-- BMC or a similar platform component will read RECOVERY_STATUS register
		//-- to check if the recovery is completed.
		//-- The I3C device will return 0x3 to indicate recovery is completed.

		data = new[2];
		data[0] = 0;
		for (int i = 0; i < 300; i++) begin
			test_log.substep($psprintf("Reading RECOVERY_STATUS register .. count 'd %0d", i));
			i3c_read(recovery_target_addr, `I3C_CORE_RECOVERY_STATUS, 2, data);
				
				// 0x0: Not in recovery mode
				// 0x1: Awaiting recovery image
				// 0x2: Booting recovery image
				// 0x3: Recovery successful
				// 0xc: Recovery failed
				// 0xd: Recovery image authentication error
				// 0xe: Error entering  Recovery mode (might be administratively disabled)
				// 0xf: Invalid component address space

				case (data[0])
					'h0: test_log.substep("Not in recovery mode");
					'h1: begin
							test_log.substep($psprintf("Awaiting recovery image.. wait loop count : 'd %0d", i));
						 end
					'h2: test_log.substep($psprintf("Booting recovery image .. wait loop count : 'd %0d", i));
					'h3: begin
							test_log.substep("Recovery successful");
							break;
						 end
					'hc: begin
							test_log.substep("Recovery failed");
							break;
						 end
					'hd: begin
							test_log.substep("Recovery image authentication error");
							break;
					 	 end
					'he: begin
							test_log.substep("Error entering  Recovery mode (might be administratively disabled)");
							break;
						 end
					'hf: begin
							test_log.substep("Invalid component address space");
						 	break;
						 end
					default: begin 
							test_log.substep("Unknown status");
							break;
						 end
				endcase

			#1us;

		end

		test_log.step("=============================================================");
		test_log.step("Step 5: Recovery completed");

	endtask

endclass