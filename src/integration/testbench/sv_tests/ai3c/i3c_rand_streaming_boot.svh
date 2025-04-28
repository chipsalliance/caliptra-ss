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
		err_count = 0;
	endfunction

	virtual task test_body();

		bit [7:0] data[];
		bit [7:0] exp_data[];

		//-- Read image from hex file
		read_image();
		//-- I3C bus initialization and address assignment
		i3c_bus_init();

		test_log.step("=============================================================");
		test_log.step("Step 1: Reading Base Registers");

		test_log.substep("Reading PROT_CAP register");
		
		exp_data = new[15];
		exp_data = '{'h4f, 'h43, 'h50, 'h20, 'h52, 'h45, 'h43, 'h56, 'h01, 'h01, 'h00, 'h00, 'h00, 'h00, 'h00};
		exp_data[10] |= 1 << 7; //-- Push C-image support
		exp_data[11] |= 1 << (11 - 8); //-- flashless boot (From RESET)
		exp_data[11] |= 1 << (12 - 8); //-- FIFO CMS support (INDIRECT_FIFO_CTRL)
		i3c_read(recovery_target_addr, `I3C_CORE_PROT_CAP, 15, data);
		check_data(data, exp_data, 15);

		test_log.substep("Reading DEVICE_ID register");
		i3c_read(recovery_target_addr, `I3C_CORE_DEVICE_ID, 24, data);
	
        test_log.substep("Reading HW_STATUS register");
		i3c_read(recovery_target_addr, `I3C_CORE_HW_STATUS, 4, data);

		test_log.substep("Reading DEVICE_STATUS register");
		i3c_read(recovery_target_addr, `I3C_CORE_DEVICE_STATUS, 7, data);

		test_log.step("=============================================================");
		test_log.step("Step 2: waiting for recovery start");

		//-- reading device status
		//-- DEVICE_STATUS ('d36)
		data = new[8];
		data[0] = 0;
		test_log.substep($psprintf("Reading DEVICE_STATUS register"));
		for(int i = 0; i < 100; i++) begin
			i3c_read(recovery_target_addr, `I3C_CORE_DEVICE_STATUS, 7, data);
			if(data[0] == 'h3) begin
				test_log.substep($psprintf("Recovery started : 'd %0d", data[0]));
				break;
			end
			#1us;
		end
		if(data[0] != 'h3) begin	
			test_log.substep("Error : Recovery did not start");
			err_count++;
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
		data[1] = 'h1; // Reset field set to 1

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
		test_log.substep($psprintf("Remaining Image Size (in bytes): 'd %0d", remaining_img_sz_in_bytes));

		if(wr_count_256B > 0) begin
		
			test_log.substep($psprintf("Writing 'd %0d of 256B blocks", wr_count_256B));

			for(int i = 0; i < wr_count_256B; i++) begin

				test_log.step($psprintf("INDIRECT_FIFO_DATA write..'d %0d", i));
				data = new[256];
				for(int k = 0; k < 16; k++) begin
					line = "'h ";
					//-- writing 16 bytes of data
					for(int j = 0; j < 16; j++) begin
						data[k*16+j] = image[i*16+k][j];
						line = $psprintf("%s%2.0h", line, data[k*16+j]);
					end
					test_log.substep($psprintf("== Image['d %0d]: %s", (i*16+k), line));
					remaining_img_sz_in_bytes = remaining_img_sz_in_bytes - 16;
				end
				test_log.substep($psprintf("Sending random write to INDIRECT_FIFO_DATA register"));	
				i3c_random_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_DATA, data, 256);

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
				
		end

		//-- writing INDIRECT_FIFO_DATA register for 16B
		if(wr_count_16B > 0) begin
			test_log.substep($psprintf("Writing 'd %0d of 16B blocks", wr_count_16B));
		
			for(int i = 0; i < wr_count_16B; i++) begin

				test_log.step($psprintf("INDIRECT_FIFO_DATA write..'d %0d / %0d", i, wr_count_16B));
				data = new[16];
				line = "'h ";
				//-- writing 16 bytes of data
				for(int j = 0; j < 16; j++) begin
					data[j] = image[(wr_count_256B*16)+i][j];
					line = $psprintf("%s%0h", line, data[j]);
				end
				test_log.substep($psprintf("Image['d %0d]: %s", i, line));
				test_log.substep($psprintf("Sending write to INDIRECT_FIFO_DATA register"));
				i3c_random_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_DATA, data, 16);
				remaining_img_sz_in_bytes = remaining_img_sz_in_bytes - 16;
			end
				
			test_log.substep($psprintf("Remaining Image Size (in bytes): 'd %0d / 'd %0d", remaining_img_sz_in_bytes, img_sz));


		end

		//-- writing INDIRECT_FIFO_DATA register for 4B
		if(wr_count_4B > 0) begin

			test_log.substep($psprintf("Writing 'd %0d of 4B blocks", wr_count_4B));
			data = new[wr_count_4B*4];
			line = "'h ";
			for(int i = 0; i < (wr_count_4B*4); i++) begin	
				data[i] = image[(wr_count_256B*16)+(wr_count_16B)][i];
				line = $psprintf("%s%0h", line, data[i]);
				remaining_img_sz_in_bytes = remaining_img_sz_in_bytes - 4;
			end
			test_log.substep($psprintf("Image['d %0d]: %s", ((wr_count_256B*16)+(wr_count_16B)), line));
			test_log.substep($psprintf("Sending write to INDIRECT_FIFO_DATA register"));
			i3c_write(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_DATA, data, (wr_count_4B*4));
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
		for (int i = 0; i < 100; i++) begin
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

			//-- BIT 0-3 : Recovery Status Code
			//-- BIT 4-7 : Image Index
			test_log.substep($psprintf("Recovery Status Code : 0x%0h", data[0]));

			case (data[0])
				'h0: 
					begin
						test_log.substep("Recovery Status Code : 0x0: Not in recovery mode");
						err_count++;
						break;
					end
				'h1: 
					begin
						test_log.substep($psprintf("Awaiting recovery image.. wait loop count : 'd %0d", i));
						if (i == 99) begin
							test_log.substep("Error : Recovery did not start");
							err_count++;
						end
					end
				'h2:
					begin
						test_log.substep($psprintf("Booting recovery image .. wait loop count : 'd %0d", i));
						if (i == 149) begin
							test_log.substep("Error : Recovery did not start");
							err_count++;
						end
					end
				'h3: 
					begin
						test_log.substep("Recovery successful");
						break;
					end
				'hc: 
					begin
						test_log.substep("Recovery failed");
						err_count++;
						break;
					end
				'hd: 
					begin
						test_log.substep("Recovery image authentication error");
						err_count++;
						break;
					end
				'he: 
					begin
						test_log.substep("Error entering  Recovery mode (might be administratively disabled)");
						err_count++;
						break;
					end
				'hf: 
					begin
						test_log.substep("Invalid component address space");
						err_count++;
						break;
					end
				'h11: 
					begin
						test_log.substep("Recovery Image Authentication : Successful, waiting for new image");
						test_log.substep($psprintf("Recovery Status Data Byte[0] : 0x%0h", data[0]));
						break;
					end	
				default: 
					begin 
						test_log.substep($psprintf("Unknown recovery status : 0x%0h", data[0]));
						err_count++;
						break;
					end
			endcase

			#1us;

		end

		test_log.step("=============================================================");
		test_log.step("Step 5: Recovery completed");

		process_test_result();

	endtask

endclass
