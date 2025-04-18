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
      .DUT type: slave 
      .Checklist items:
      .Spec section: 
      5.1.4 Bus Initialization and Dynamic Address Assignment Mode
      .Procedure: 
            * Device State For Test: 
            * Overview of Test Steps:
      1. Wait for Dynamic Address Assignment and Bus Initialization done
      2. Send random write transfer
      3. Send random read transfer
      4. Send random transfer
      .Result:
      1. Main Master can do read/write transfer to each slave
*/

// FIXME: REMOVE HARDCODED PATH
`include "/cad/tools/mentor/avery/2025.1/i3cxactor-2025.1/src.i3c/ai3c_enum.svh"

class random_len_helper;
    rand int random_len[];  // Declare as class member
    int total_length;               // Length of the data to be written

    constraint len_c {
        random_len.sum() == total_length;
        random_len.size() > 0;
		random_len.size() <= 10;
        foreach (random_len[i]) { random_len[i] inside {4, 8, 16, 32, 64}; }
    }
    function new(int length);
        this.total_length = length;
    endfunction
endclass

class cptra_ss_i3c_core_base_test extends ai3ct_base;

	`avery_test_reg(cptra_ss_i3c_core_base_test)
    random_len_helper random_lengths;  // Create an instance

	// -- I3C Target Addresses
	ai3c_addr_t general_target_addr;
	ai3c_addr_t recovery_target_addr;

	//-- image variables
	bit [31:0] cmdline_img_sz;
	bit [31:0] img_sz;
	int fp;
	string line;
	int i = 0;
	bit [7:0] read_mem[8192][16];
	bit [7:0] image[][];
	int img_sz_in_16B;
	int img_sz_in_4B;
	int wr_count_256B;
	int wr_count_16B;
	int wr_count_4B;
	int wr_count_1B;
	int r;
	
	
	bit [31:0] remaining_img_sz_in_bytes;
    function new(string name, `avery_xvm_parent);
        super.new("cptra_ss_i3c_core_base_test", parent);
	endfunction

	task pre_bfm_started();
		if (!chk_test_app("has_i3c_slv"))
			return;
	endtask

    virtual function bit [7:0] crc8 ( bit [7:0] data [], bit [7:0] crc_prv = '0 );
        automatic bit [7:0] crc = crc_prv;

        for (int i=0; i<data.size(); i=i+1) begin
            automatic bit [7:0] dat = data[i];
            automatic bit [7:0] crc_new;

            crc_new[0] = crc[0] ^ crc[6] ^ crc[7] ^ dat[0] ^ dat[6] ^ dat[7];
            crc_new[1] = crc[0] ^ crc[1] ^ crc[6] ^ dat[0] ^ dat[1] ^ dat[6];
            crc_new[2] = crc[0] ^ crc[1] ^ crc[2] ^ crc[6] ^ dat[0] ^ dat[1] ^ dat[2] ^ dat[6];
            crc_new[3] = crc[1] ^ crc[2] ^ crc[3] ^ crc[7] ^ dat[1] ^ dat[2] ^ dat[3] ^ dat[7];
            crc_new[4] = crc[2] ^ crc[3] ^ crc[4] ^ dat[2] ^ dat[3] ^ dat[4];
            crc_new[5] = crc[3] ^ crc[4] ^ crc[5] ^ dat[3] ^ dat[4] ^ dat[5];
            crc_new[6] = crc[4] ^ crc[5] ^ crc[6] ^ dat[4] ^ dat[5] ^ dat[6];
            crc_new[7] = crc[5] ^ crc[6] ^ crc[7] ^ dat[5] ^ dat[6] ^ dat[7];

            crc = crc_new;
        end

        return crc;
    endfunction

	function ai3c_transaction gen_dc_ccc_cmd(
        input ai3c_ccc_e  dc_ccc,
        ref   ai3c_addr_t das[$]
        );
        ai3c_transaction tr;
        string           s;
        bit              ok;

        tr = new(sys_agt.mgr, 1);
        ok = tr.randomize () with {
            ccc        == dc_ccc;
            mhs.size() == das.size() + 1;
            foreach (das[i]) {
                mhs[i+1].addr == das[i];
            }
            // TODO: for specify CCC, give special value, EXP. SETMRL ...
        };
        if (!ok) begin
            foreach (das[i])
                s = {s, $psprintf("  da[%0d]: 'h%h", i, das[i])};
            test_log.fatal($psprintf("Randomization failed, dc_ccc:%s, das size:%0d\n", dc_ccc.name, das.size()));
        end
        return tr;
    endfunction

	virtual task i3c_send_dc_ccc_setmrl();
		ai3c_transaction tr;
		ai3c_addr_t addr[$];
		test_log.step("=================================================================");
		test_log.step("Sending DC CCC SETMRL command");
		addr.push_back(sys_agt.mgr.dev_infos[0].da);
		addr.push_back(sys_agt.mgr.dev_infos[0].da);
		// tr = gen_dc_ccc_cmd(AI3C_CCC_SETMRL, addr);
		tr = gen_dc_ccc_cmd(AI3C_CCC_DC_SETMRL, addr);
		sys_agt.post_transaction(tr);
		tr.wait_done(20us);
		chk_tr(tr);
		test_log.step($psprintf("DC CCC SETMRL command sent to device 'h %0h", addr[0]));
	endtask
	
	virtual task i3c_bus_init();

		test_log.step("=================================================================");
		test_log.step("Waiting for Dynamic Address Assignment and Bus Initialization");
		sys_agt.wait_event("bus_init_done", 1ms);
		test_log.step("Dynamic Address Assignment and Bus Initialization done");
		test_log.sample(AI3C_5_1_2_1n3);
		test_log.sample(AI3C_5_1_2_2n1);

		//-- grabbing dynamic address for the I3C core
		test_log.step($sformatf("I3C device count: %0d", sys_agt.mgr.dev_infos.size()));
		foreach (sys_agt.mgr.dev_infos[i]) begin
			case(sys_agt.mgr.dev_infos[i].sa)
				'h5A: begin
					// general_target_addr= sys_agt.mgr.i3c_dev_das[i];
					general_target_addr= sys_agt.mgr.dev_infos[i].da;
					test_log.substep($sformatf("I3C device 'd %0d: static addr 'h %0h, dynamic addr 'h %0h", i,sys_agt.mgr.dev_infos[i].sa, general_target_addr));
				end
				'h5B: begin
					// recovery_target_addr = sys_agt.mgr.i3c_dev_das[i];
					recovery_target_addr = sys_agt.mgr.dev_infos[i].da;
					test_log.substep($sformatf("I3C device 'd %0d: static addr 'h %0h, dynamic addr 'h %0h", i,sys_agt.mgr.dev_infos[i].sa, recovery_target_addr));
				end
				default: begin
					//-- print error message if the static address is not 0x5A or 0x5B
					test_log.substep($sformatf(" ERROR : I3C device %0d: static addr 'h %0h is not 0x5A or 0x5B", i, sys_agt.mgr.dev_infos[i].sa));
				end
			endcase
		end
		test_log.substep($sformatf("I3C Subordinate Recovery addr 'h %0h", recovery_target_addr));
		test_log.substep($sformatf("I3C Subordinate General addr 'h %0h", general_target_addr));

	endtask

	virtual task read_image();

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
	endtask

	virtual task i3c_write( input ai3c_addr_t addr,
					input bit[7:0] cmd,
					input bit[7:0] data[],
					input int      len,
					input string    wr_type = "RECOVERY");

		ai3c_transaction tr;
       	ai3c_message    msg;
       	bit [7:0]       pec;

        time timeout;
        timeout = (len * 2us) + 20us;

		test_log.step($psprintf("I3C wr txfer started at...: addr = 'h %0h, len = 'd %0d", addr, len));

		tr = new(`avery_strarg sys_agt.mgr);
       	tr.mhs[0].addr = addr;
       	tr.mhs[0].rw   = AI3C_write;
       	tr.mhs[0].len  = len + (wr_type == "RECOVERY"? 4 : 1); // added 4 bytes for cmd, legnth lsb, length msb, and pec
       	tr.msgs[0]     = new(tr.mhs[0], tr);
       	msg            = tr.msgs[0];

		if(wr_type == "RECOVERY") begin
			pec = crc8('{addr << 1, cmd, len, 0});
			pec = crc8(data, pec);

			for(int i = 0; i < len + 4; i++) begin
				if(i==0) 	  		msg.data_bytes[i] = cmd;        // cmd byte [0th byte]
				else if(i==1) 		msg.data_bytes[i] = len;        // cmd lsb  [1st byte]
				else if(i==2) 		msg.data_bytes[i] = 0;          // cmd msb  [2nd byte]
				else if(i==len+3)   msg.data_bytes[i] = pec;        // pec byte [nth byte]
				else 				msg.data_bytes[i] = data[i-3];  // data bytes [3rd to nth byte]
			end
		end else begin
			pec = '0;
			pec = crc8(data, pec);
			for(int i = 0; i < len + 1; i++) begin
				if(i==len)			msg.data_bytes[i] = pec;	  // pec byte [nth byte]
				else 				msg.data_bytes[i] = data[i];  // data bytes [3rd to nth byte]
			end
		end

		test_log.substep($psprintf("Writing data:\n%s", tr.sprint(2)));

		sys_agt.post_transaction(tr);
       	tr.wait_done(timeout);
       	chk_tr(tr);
       	test_log.step($psprintf("I3C wr txfer completed at.: addr = 'h %0h, len = 'd %0d", addr, len));

	endtask

    virtual task i3c_random_write(
        input ai3c_addr_t addr,
        input bit[7:0] cmd,
        input bit[7:0] data[],
        input int      len);

        bit [7:0] data_subset[];
        int data_idx;
        // int wr_len[];

        //-- create a new instance of RandomWriteHelper
        random_lengths = new(len);
        assert(random_lengths.randomize());  // Randomize wr_len
        // wr_len = new[random_lengths.random_len.size()];  // Retrieve randomized values
        // test_log.substep($psprintf("Randomized write lengths: %0d", wr_len.size()));
        foreach (random_lengths.random_len[i]) begin
            test_log.substep($psprintf("Randomized write length %0d: %0d", i, random_lengths.random_len[i]));
        end

        //-- perform write with each random_lengths.random_len
        foreach (random_lengths.random_len[i]) begin
            test_log.substep($psprintf("Writing %0d bytes", random_lengths.random_len[i]));
            data_subset = new[random_lengths.random_len[i]];
            data_idx = 0;
            for (int j = 0; j < i; j++) begin
                data_idx += random_lengths.random_len[j];
            end
            test_log.substep($psprintf("starting data_index = %0d, andom_lengths.random_len[%0d] = %0d", data_idx, i, random_lengths.random_len[i]));
            for (int j = 0; j < random_lengths.random_len[i]; j++) begin
                data_subset[j] = data[data_idx + j];
            end
            i3c_write(addr, cmd, data, random_lengths.random_len[i]);
        end
        test_log.substep($psprintf("Completed writing %0d bytes in %0d chunks", len, random_lengths.random_len.size()));

    endtask

	virtual task i3c_read(	input ai3c_addr_t  addr,
					input bit [7:0]    cmd,
					input int   	   len,
					output bit [7:0] data[]);

		ai3c_transaction tr;
		ai3c_message     msg;
		bit              ok;
		// bit [7:0]        data[];
        bit [7:0]        pec;

        time timeout;
        timeout = (len * 2us) + 20us;

		test_log.step($psprintf("I3C rd txfer started at...: addr = 'h %0h, len = 'd %0d", addr, len));
		tr = new(`avery_strarg sys_agt.mgr);
		ok = tr.randomize () with {
				mhs.size() == 2;
				mhs.size() == 2 -> mhs[0].addr == addr;
				mhs.size() == 2 -> mhs[0].rw   == AI3C_write;
				mhs.size() == 2 -> mhs[0].len  == 2;
				mhs.size() == 2 -> mhs[1].addr == addr;
				mhs.size() == 2 -> mhs[1].rw   == AI3C_read;
                mhs.size() == 2 -> mhs[1].len  == len + 3; // Account for len lsb+msb and PEC
		};

		if (!ok) begin 
				test_log.fatal($psprintf("%m: randomization failed"));
		end

        pec = crc8('{addr << 1, cmd});

		msg = tr.msgs[0];
		msg.data_bytes[0] = cmd;
		msg.data_bytes[1] = pec;
		test_log.substep($psprintf("Transfer:\n%s", tr.sprint(2)));

		sys_agt.post_transaction(tr);
		tr.wait_done(timeout);

		//-- read data from the subordinate
		msg = tr.msgs[1];
		data = new[len];
		foreach(msg.data_bytes[i]) begin
            data[i] = msg.data_bytes[2 + i]; // Account for len lsb+msb
            test_log.substep($psprintf("Data Read : 'h %0h", msg.data_bytes[i]));
		end

        pec = crc8('{(addr << 1) | 1}); // address
        pec = crc8('{msg.data_bytes[0], msg.data_bytes[1]}, pec); // len
        pec = crc8(data, pec); // payload

		test_log.substep($psprintf("Addr      : 'h %0h ", addr));
		test_log.substep($psprintf("Length    : 'h %0h ", len));
		test_log.substep($psprintf("Data Read :\n%s", tr.sprint(2)));

        test_log.substep($psprintf("PEC recvd : 'h %0h", msg.data_bytes[2+len]));
        test_log.substep($psprintf("PEC calcd : 'h %0h", pec));

        if (pec != msg.data_bytes[2+len])
            test_log.substep("Received PEC mismatch!");
			
		chk_tr(tr);
		test_log.step($psprintf("I3C rd txfer completed at.: addr = 'h %0h, len = 'd %0d", addr, len));

	endtask

    virtual task check_data(
        input bit [7:0] data[],
        input bit [7:0] expected_data[],
        input int       len
    );
        for (int i = 0; i < len; i++) begin
            if (data[i] != expected_data[i]) begin
                test_log.substep($psprintf("Error : Data mismatch at index %0d: expected 'h %0h, got 'h %0h", i, expected_data[i], data[i]));
            end
        end
    endtask

	virtual task test_body();

		bit [7:0] data[];

		//-- I3C bus initialization and address assignment
		i3c_bus_init();

		test_log.step("=============================================================");
		test_log.step("Step 1: Reading Base Registers");

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
		i3c_read(recovery_target_addr, `I3C_CORE_INDIRECT_FIFO_CTRL, 6, data);
		test_log.substep($psprintf("Received data:"));
		foreach(data[i]) begin
			test_log.substep($psprintf("data[%0d] = 'h %0h", i, data[i]));
		end

		test_log.step("=============================================================");
		test_log.step("I3C Reg Read & Write test completed");

	endtask

endclass