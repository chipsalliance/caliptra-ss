/*
 * |-----------------------------------------------------------------------|
 * |                                                                       |
 * |   Copyright Avery Design Systems, Inc. 2016.           |
 * |     All Rights Reserved.       Licensed Software.           |
 * |                                                                       |
 * |                                                                       |
 * | THIS IS UNPUBLISHED PROPRIETARY SOURCE CODE OF AVERY DESIGN SYSTEMS   |
 * | The copyright notice above does not evidence any actual or intended   |
 * | publication of such source code.           |
 * |                                                                       |
 * |-----------------------------------------------------------------------|
 */
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

class ai3ct_ext_basic extends ai3ct_base;

	`avery_test_reg(ai3ct_ext_basic)

	function new(string name, `avery_xvm_parent);
        super.new("ai3ct_ext_basic", parent);
	endfunction

	task pre_bfm_started();
       if (!chk_test_app("has_i3c_slv"))
		return;
    endtask

    function bit [7:0] crc8 ( bit [7:0] data [], bit [7:0] crc_prv = '0 );
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

	task i3c_write( input ai3c_addr_t addr,
					input bit[7:0] cmd,
					input bit[7:0] data[],
					input int      len);
       
		ai3c_transaction tr;
       	ai3c_message    msg;
       	bit [7:0]       pec;

		test_log.step($psprintf("I3C wr txfer started at...: addr = %0h, len = %0d", addr, len));
       	
		tr = new(`avery_strarg sys_agt.mgr);
       	tr.mhs[0].addr = addr;
       	tr.mhs[0].rw   = AI3C_write;
       	tr.mhs[0].len  = len + 4; // added 4 bytes for cmd, legnth lsb, length msb, and pec
       	tr.msgs[0]     = new(tr.mhs[0], tr);
       	msg            = tr.msgs[0];

        pec = crc8('{addr << 1, cmd, len, 0});
        pec = crc8(data, pec);

		for(int i = 0; i < len + 4; i++) begin
			if(i==0) 	  		msg.data_bytes[i] = cmd;        // cmd byte [0th byte]
			else if(i==1) 		msg.data_bytes[i] = len;        // cmd lsb  [1st byte]
			else if(i==2) 		msg.data_bytes[i] = 0;          // cmd msb  [2nd byte]
			else if(i==len+3)   msg.data_bytes[i] = pec;        // pec byte [nth byte]
			else 				msg.data_bytes[i] = data[i-3];  // data bytes [3rd to nth byte]
		end

		test_log.substep($psprintf("Writing data:\n%s", tr.sprint(2)));

		sys_agt.post_transaction(tr);
       	tr.wait_done(32us);
       	chk_tr(tr);
       	test_log.step($psprintf("I3C wr txfer completed at.: addr = %0h, len = %0d", addr, len));
	
	endtask

	task i3c_read(	input ai3c_addr_t  addr,
					input bit [7:0]    cmd,
					input int   	   len,
					output bit [7:0] data[]);

		ai3c_transaction tr;
		ai3c_message     msg;
		bit              ok;
		// bit [7:0]        data[];
        bit [7:0]        pec;

		test_log.step($psprintf("I3C rd txfer started at...: addr = %0h, len = %0d", addr, len));
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
		tr.wait_done(100us);

		//-- read data from the subordinate
		msg = tr.msgs[1];
		data = new[len];
		foreach(msg.data_bytes[i]) begin
            data[i] = msg.data_bytes[2 + i]; // Account for len lsb+msb
            test_log.substep($psprintf("Data Read : %0h", msg.data_bytes[i]));
		end

        pec = crc8('{(addr << 1) | 1}); // address
        pec = crc8('{msg.data_bytes[0], msg.data_bytes[1]}, pec); // len
        pec = crc8(data, pec); // payload

		test_log.substep($psprintf("Addr      : %0h ", addr));
		test_log.substep($psprintf("Length    : %0h ", len));
		test_log.substep($psprintf("Data Read :\n%s", tr.sprint(2)));

        test_log.substep($psprintf("PEC recvd : %0h", msg.data_bytes[2+len]));
        test_log.substep($psprintf("PEC calcd : %0h", pec));

        if (pec != msg.data_bytes[2+len])
            test_log.substep("Received PEC mismatch!");

		test_log.step($psprintf("I3C rd txfer completed at.: addr = %0h, len = %0d", addr, len));

	endtask


	virtual task test_body();

		ai3c_addr_t general_target_addr;
		ai3c_addr_t recovery_target_addr;
		ai3c_addr_t addr = 8'h5A;
		bit ok;
		bit [7:0] data[];

		test_log.step("=================================================================");
		test_log.step("Wait for Dynamic Address Assignment and Bus Initialization");
		sys_agt.wait_event("bus_init_done", 1ms);
		test_log.step("Dynamic Address Assignment and Bus Initialization done");
		test_log.sample(AI3C_5_1_2_1n3);
		test_log.sample(AI3C_5_1_2_2n1);

		//-- grabbing dynamic address for the I3C core
		recovery_target_addr = sys_agt.mgr.i3c_dev_das[0]; // get 0 slave
		general_target_addr = sys_agt.mgr.i3c_dev_das[1]; // get 1 slave
		addr = recovery_target_addr;
		test_log.substep($psprintf("I3C Subordinate dynamic addr 'h%0h", addr));

		test_log.step("=============================================================");
		test_log.step("Step 1: Reading Base Registers");

		test_log.substep("Reading PROT_CAP register");
		i3c_read(addr, 'd34, 16, data);
		test_log.substep("Reading DEVICE_ID register");
		i3c_read(addr, 'd35, 24, data);
		test_log.substep("Reading HW_STATUS register");
		i3c_read(addr, 'd37, 4, data);

		
		test_log.step("=============================================================");
		test_log.step("Step 2: waiting for recovery start");

		//-- reading device status
		//-- DEVICE_STATUS ('d36)
		data = new[1];
		data[0] = 0;
		for(int i = 0; i < 100; i++) begin
			i3c_read(addr, 'd36, 1, data);
			if(data[0] == 'h3) begin
				test_log.substep($psprintf("Recovery started : %0d", data[0]));
				break;
			end
			#10us;
		end
		if(data[0] != 'h3) begin
			test_log.substep("Recovery did not start");
		end

		//-- Reading RECOVERY_STATUS register
		i3c_read(addr, 'd36, 1, data);
		if(data[0] == 'h1) begin
			test_log.substep("Recovery in progress");
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
		i3c_write(addr, 'd38, data, 'h3);

		//-- writing INDIRECT_FIFO_CTRL register
		//-- INDIRECT_FIFO_CTRL ('d45)
		//-- Step 7:
		//-- BMC or a similar platform component will update INDIRECT_FIFO_CTRL 
		//-- with Component Memory Space (CMS) byte 0 with 0x0, 
		//-- Reset field byte 1 with 0x1 and 
		//-- Image size byte 2 to 5 field to size of the image.
		data = new[6];
		data[0] = 'h0; // CMS set to 0
		data[1] = 'h1; // FIFO 
		data[2] = 'd4; // Image size 0 (4 x 32-bit / 4 x 4B) FIXME: Hardcoded
		data[3] = 'd0; // Image size 1
		data[4] = 'd0; // Image size 2
		data[5] = 'd0; // Image size 3
		test_log.substep($psprintf("Sending write to INDIRECT_FIFO_CTRL register"));
		i3c_write(addr, 'd45, data, 6);

		// -- Harded the length of image to 4 x 32-bit
		for(int i = 0; i < 1; i++) begin
			
			//-- writing INDIRECT_FIFO_DATA register
			//-- Step 8:
			//-- BMC or a similar platform component writes to INDIRECT_FIFO_DATA register. 
			//-- I3C device shall return a NACK response for any transfer that would cause 
			//-- the Head Pointer to advance to equal the Tail Pointer. 
			//-- BMC can implement flow control through NACK responses. 

			test_log.step($psprintf("INDIRECT_FIFO_DATA write..%0d", i));
			
			data = new[16];
			for(int i = 0; i < 16; i++)
					data[i] = 'd00 + i;
			test_log.substep($psprintf("Sending write to INDIRECT_FIFO_DATA register"));
			i3c_write(addr, 'd47, data, 16);

			//-- read INDIRECT_FIFO_STAUTS register
			//-- INDIRECT_FIFO_STATUS ('d46)
			//-- Step 9:
			//-- The I3C device will keep head and tail pointers along with 
			//-- FIFO status up to date into INDIRECT_FIFO_STATUS register. 
			//-- I3C recovery interface HW wait for an update to 
			//-- INDIRECT_DATA_REG with 1-256B data from BMC.
			data[0] = 0;
			for(int i = 0; i < 100; i++) begin
				i3c_read(addr, 'd46, 20, data);
				if(data[0] == 'h1) begin
					test_log.substep("Indirect FIFO is empty");
					break;
				end
				#1us;
			end
			if(data[0] != 'h1) begin
				test_log.substep("Indirect FIFO is not empty");
			end

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
		data[0] = 'h0; // Component Memory Space (CMS)
		data[1] = 'h0; // Use Recovery Image from memory window (CMS)
		data[2] = 'h1; // activate recovery image
		test_log.substep($psprintf("Sending write to RECOVERY_CTRL register"));
		i3c_write(addr, 'd38, data, 'h3);
		
		//-- reading RECOVERY_STATUS register
		//-- RECOVERY_STATUS ('d36)
		//-- Step 14:
		//-- BMC or a similar platform component will read RECOVERY_STATUS register
		//-- to check if the recovery is completed.
		//-- The I3C device will return 0x3 to indicate recovery is completed.

		data = new[1];
		data[0] = 0;
		for (int i = 0; i < 3; i++) begin
			i3c_read(addr, 'd36, 1, data);
			if(data[0] == 'h3) begin
				test_log.substep($psprintf("Recovery completed : %0d", data[0]));
				test_log.substep("Recovery successful");
				break;
			end
			#10us;
		end
		if(data[0] != 'h3) begin
			test_log.substep("Recovery failed");
		end

		test_log.step("=============================================================");
		test_log.step("Step 5: Recovery completed");

	endtask

endclass
