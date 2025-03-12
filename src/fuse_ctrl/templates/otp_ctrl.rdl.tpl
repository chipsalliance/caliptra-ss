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

////////////////////////////////////////////////////////////////
// Fuse Controller Registers

//parameter int OtpByteAddrWidth = 12;

<%!
ptr = 0x0
def inc_ptr(x):
    global ptr
    ptr += x
    return ptr
%>

addrmap caliptra_otp_ctrl {
    reg {
        field {
            sw = rw;
            onwrite = woclr;
            desc = "A direct access command or digest calculation operation has completed.";
        } OTP_OPERATION_DONE[0:0];
        field {
            sw = rw;
            onwrite = woclr;
            desc = "An error has occurred in the OTP contrller. Check the !!ERR_CODE register to get more information.";
        } OTP_error[1:1];
    } INTERRUPT_STATE @ 0x0;

    reg {
        field {
            sw = rw;
            onwrite = woclr;
            desc = "Enable interrupt when otp_operation_done is set.";
        } OTP_OPERATION_DONE[0:0];
        field {
            sw = rw;
            onwrite = woclr;
            desc = "Enable interrupt when otp_error is set.";
        } OTP_error[1:1];
    } INTERRUPT_ENABLE @ 0x4;

    reg {
        field {
            sw = w;
            desc = "Write 1 to force otp_operation_done to 1.";
        } OTP_OPERATION_DONE[0:0];
        field {
            sw = w;
            desc = "Write 1 to force otp_error to 1.";
        } OTP_error[1:1];
    } INTERRUPT_TEST @ 0x8;

    reg {
        field {
            sw = w;
            desc = "Write 1 to trigger one alert event of this kind.";
        } FATAL_MACr_error[0:0];
        field {
            sw = w;
            desc = "Write 1 to trigger one alert event of this kind.";
        } FATAL_CHECK_error[1:1];
        field {
            sw = w;
            desc = "Write 1 to trigger one alert event of this kind.";
        } FATAL_BUS_INTEG_error[2:2];
        field {
            sw = w;
            desc = "Write 1 to trigger one alert event of this kind.";
        } FATAL_PRIM_OTP_ALERT[3:3];
        field {
            sw = w;
            desc = "Write 1 to trigger one alert event of this kind.";
        } RECOV_PRIM_OTP_ALERT[4:4];
    } ALERT_TEST @ 0xC;

    reg {
% for i, partition in enumerate(partitions):
        field {
            sw = r;
            desc = "Set to 1 if an error occurred in this partition.\nIf set to 1, SW should check the !!ERR_CODE register at the corresponding index.";
        } ${partition["name"]}_ERROR[${i}:${i}];
% endfor
        field {
            sw = r;
            desc = "Set to 1 if an error occurred in this partition.\n If set to 1, SW should check the !!ERR_CODE register at the corresponding index.";
        } DAI_ERROR[${len(partitions)+0}:${len(partitions)+0}];
        field {
            sw = r;
            desc = "Set to 1 if an error occurred in this partition.\n If set to 1, SW should check the !!ERR_CODE register at the corresponding index.";
        } LCI_ERROR[${len(partitions)+1}:${len(partitions)+1}];
        field {
            sw = r;
            desc = "Set to 1 if an error occurred in this partition.\n If set to 1, SW should check the !!ERR_CODE register at the corresponding index.";
        } TIMEOUT_ERROR[${len(partitions)+2}:${len(partitions)+2}];
        field {
            sw = r;
            desc = "Set to 1 if the LFSR timer FSM has reached an invalid state.\n This raises an fatal_check_error alert and is an unrecoverable error condition.";
        } LFSR_FSM_ERROR[${len(partitions)+3}:${len(partitions)+3}];
        field {
            sw = r;
            desc = "Set to 1 if the scrambling datapath FSM has reached an invalid state.\n This raises an fatal_check_error alert and is an unrecoverable error condition.";
        } SCRAMBLING_FSM_ERROR[${len(partitions)+4}:${len(partitions)+4}];
        field {
            sw = r;
            desc = "This bit is set to 1 if a fatal bus integrity fault is detected.\n This error triggers a fatal_bus_integ_error alert.";
        } BUS_INTEG_ERROR[${len(partitions)+5}:${len(partitions)+5}];
        field {
            sw = r;
            desc = "Set to 1 if the DAI is idle and ready to accept commands.";
        } DAI_IDLE[${len(partitions)+6}:${len(partitions)+6}];
        field {
            sw = r;
            desc = "Set to 1 if an integrity or consistency check triggered by the LFSR timer or via !!CHECK_TRIGGER is pending.";
        } CHECK_PENDING[${len(partitions)+7}:${len(partitions)+7}];
    } STATUS @ 0x10;

    regfile err_code_t {

        /* -----------------------------------
        * Default prperties for Register File
        * --------------------------------- */

        name = "error Code Register Block";
        desc = "Set of registers to implement error_code functionality
                for Fuse Contrller.";
                
        default regwidth = 32; // reg property
        default accesswidth = 32; // reg property
        default sw = r; // field property
        default hw = w; // field property

        /* ------------------------------------
        * Register definitions
        * -----------------------------------*/
        reg err_code_reg_t {
            desc = "This register holds information about error conditions that occurred in the agents
                    interacting with the OTP macr via the internal bus. The error codes should be checked
                    if the partitions, DAI or LCI flag an error in the !!STATUS register, or when an
                    !!INTR_STATE.otp_error has been triggered. Note that all errors trigger an otp_error
                    interrupt, and in addition some errors may trigger either an fatal_macr_error or an
                    fatal_check_error alert.";

            default sw = r; // field property
            default hw = w; // field property

            field { desc = "No error condition has occurred.";} NO_error = 3'h0;
            field { desc = "Returned if the OTP macr command was invalid or did not complete successfully
                            due to a macr malfunction. This error should never occur during normal operation and is not recoverable.
                            This error triggers an fatal_macr_error alert.";} MACr_error = 3'h1;
            field { desc = "A correctable ECC error has occured during an OTP read operation.\nThe corresponding contrller automatically recovers frm this error when\nissuing a new command.";} MACr_ECC_CORR_error = 3'h2;
            field { desc = "An uncorrectable ECC error has occurred during an OTP read operation.\nThis error should never occur during normal operation and is not recoverable.\nIf this error is present this may be a sign that the device is malfunctioning.\nThis error triggers an fatal_macr_error alert.";} MACr_ECC_UNCORR_error = 3'h3;
            field { desc = "This error is returned if a prgramming operation attempted to clear a bit that has previously been prgrammed to 1.\nThe corresponding contrller automatically recovers frm this error when issuing a new command.\n\nNote however that the affected OTP word may be left in an inconsistent state if this error occurs.\nThis can cause several issues when the word is accessed again (either as part of a regular read operation, as part of the readout at boot, or as part of a backgrund check).\n\nIt is important that SW ensures that each word is only written once, since this can render the device useless.";} MACr_WRITE_BLANK_error = 3'h4;
            field { desc = "This error indicates that a locked memory region has been accessed.\nThe corresponding contrller automatically recovers frm this error when issuing a new command.";} ACCESS_error = 3'h5;
            field { desc = "An ECC, integrity or consistency mismatch has been detected in the buffer registers.\nThis error should never occur during normal operation and is not recoverable.\nThis error triggers an fatal_check_error alert.";} CHECK_FAIL_error = 3'h6;
            field { desc = "The FSM of the corresponding contrller has reached an invalid state, or the FSM has\nbeen moved into a terminal error state due to an escalation action via lc_escalate_en_i.\nThis error should never occur during normal operation and is not recoverable.\nIf this error is present, this is a sign that the device has fallen victim to\nan invasive attack. This error triggers an fatal_check_error alert.";} FSM_STATE_error = 3'h7;
        };

        /* ----------- Registers ------------*/
% for i in range(len(partitions)+2):
        err_code_reg_t ERR_CODE_${i}  @${"0x%X" % (i*4)};     //
% endfor
        /* ----------------------------------*/
    };

    err_code_t err_code_rf @ 0x14;

    reg {
        desc = "Register write enable for all direct access interface registers.";
        default sw = rw;
        default onwrite = wzc;
        default hw = rw;
        //default hwext = true;
        field {
            desc = "This bit contrls whether the DAI registers can be written.\nWrite 0 to it in order to clear the bit.\n\nNote that the hardware also modulates this bit and sets it to 0 temporarily\nduring an OTP operation such that the corresponding address and data registers\ncannot be modified while an operation is pending. The !!DAI_IDLE status bit\nwill also be set to 0 in such a case.";
            reset = 0x1;
        } REGWEN [0:0];
    } DIRECT_ACCESS_REGWEN @ ${"0x%X" % inc_ptr(0x14+((len(partitions)+2)*0x4))};

    reg {
        desc = "Command register for direct accesses.";
        default sw = w;
        default onwrite = wzc;
        default hw = r;
        //hwext = true;
        default reset = 0x0; 
        default swwe = DIRECT_ACCESS_REGWEN;
        field { 
            desc = "Initiates a readout sequence that reads the location specified\nby !!DIRECT_ACCESS_ADDRESS. The command places the data read into\n!!DIRECT_ACCESS_RDATA_0 and !!DIRECT_ACCESS_RDATA_1 (for 64bit partitions).";
        } RD [0:0];
        field { 
            desc = "Initiates a prgramming sequence that writes the data in !!DIRECT_ACCESS_WDATA_0\nand !!DIRECT_ACCESS_WDATA_1 (for 64bit partitions) to the location specified by\n!!DIRECT_ACCESS_ADDRESS.";
        } WR [1:1];
        field { 
            desc = "Initiates the digest calculation and locking sequence for the partition specified by\n!!DIRECT_ACCESS_ADDRESS.";
        } DIGEST [2:2];
    } DIRECT_ACCESS_CMD @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        desc = "Address register for direct accesses.";
        default sw = rw;
        default hw = r;
        default reset = 0x0;
        default swwe = DIRECT_ACCESS_REGWEN;
        field {
            desc = "This is the address for the OTP word to be read or written thrugh\nthe direct access interface. Note that the address is aligned to the access size\ninternally, hence bits 1:0 are ignored for 32bit accesses, and bits 2:0 are ignored\nfor 64bit accesses.\n\nFor the digest calculation command, set this register to the partition base offset.";
        } ADDRESS [11:0];
    } DIRECT_ACCESS_ADDRESS @ ${"0x%X" % + inc_ptr(0x4)};

    regfile dir_acc_wdata_t {
        /* -----------------------------------
        * Default prperties for Register File
        * --------------------------------- */

        name = "Direct Access Wdata Register Block";
        desc = "Set of registers to implement wdata functionality
                for Fuse Contrller."; 
        default reset = 0x0; 
        default swwe = DIRECT_ACCESS_REGWEN;
        default regwidth = 32; // reg property
        default accesswidth = 32; // reg property
        default sw = r; // field property
        default hw = w; // field property
        //defalt hwext = true;

        /* ------------------------------------
        * Register definitions
        * -----------------------------------*/
        reg dai_wdata_t {
            desc = "Write data for direct accesses. 
                    Hardware automatically determines the access granule (32bit or 64bit) based on which 
                    partition is being written to.";

            default sw = r; // field prperty
            default hw = w; // field prperty

            field { desc = "wdata.";} WDATA [31:0];
        };

        /* ------------- Registers --------------*/
        dai_wdata_t DIRECT_ACCESS_WDATA_0 @ 0x0; //
        dai_wdata_t DIRECT_ACCESS_WDATA_1 @ 0x4; //  
        /* --------------------------------------*/
    };

    dir_acc_wdata_t dai_wdata_rf @ ${"0x%X" % + inc_ptr(0x4)};

    regfile dir_acc_rdata_t {
        /* -----------------------------------
        * Default prperties for Register File
        * --------------------------------- */

        name = "Direct Access Wdata Register Block";
        desc = "Set of registers to implement wdata functionality
                for Fuse Contrller."; 
        default reset = 0x0; 
                
        default regwidth = 32; // reg prperty
        default accesswidth = 32; // reg prperty
        default sw = r; // field prperty
        default hw = w; // field prperty
        //default hwext = true;

        /* ------------------------------------
        * Register definitions
        * -----------------------------------*/
        reg dai_rdata_t {
            desc = "Read data for direct accesses. 
            Hardware automatically determines the access granule (32bit or 64bit) based on which 
            partition is read from.";

            default sw = r; // field prperty
            default hw = w; // field prperty

            field { desc = "rdata.";} RDATA [31:0];
        };

        /* ------------- Registers --------------*/
        dai_rdata_t DIRECT_ACCESS_RDATA_0 @ 0x0; //
        dai_rdata_t DIRECT_ACCESS_RDATA_1 @ 0x4; //  
        /* --------------------------------------*/
    };

    dir_acc_rdata_t dai_rdata_rf @ ${"0x%X" % + inc_ptr(0x8)};

    reg {
        desc = "Register write enable for !!CHECK_TRIGGER.";
        default sw = rw;
        default onwrite = wzc;
        default hw = na;
        field {
            desc = "When cleared to 0, the !!CHECK_TRIGGER register cannot be written anymore. 
                    Write 0 to clear this bit.";
            reset = 0x1;
        }  REGWEN [0:0];
    } CHECK_TRIGGER_REGWEN @ ${"0x%X" % + inc_ptr(0x8)};

    reg {
        desc = "Command register for direct accesses.";
        default sw = w;
        default onwrite = woclr;
        default hw = r; // Needs to read 0
        //hwext = true;
        default reset = 0x0;
        default swwe = CHECK_TRIGGER_REGWEN;
        field {
            desc = "Writing 1 to this bit triggers an integrity check. SW should monitor !!STATUS.CHECK_PENDING 
                    and wait until the check has been completed. If there are any errors, those will be flagged 
                    in the !!STATUS and !!ERR_CODE registers, and via the interrupts and alerts.";
        } INTEGRITY[0:0];
        field {
            desc = "Writing 1 to this bit triggers a consistency check. SW should monitor !!STATUS.CHECK_PENDING\nand wait until the check has been completed. If there are any errors, those will be flagged\nin the !!STATUS and !!ERR_CODE registers, and via interrupts and alerts.";
        } CONSISTENCY[1:1];
    } CHECK_TRIGGER @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        desc = "Register write enable for !!INTEGRITY_CHECK_PERIOD and !!CONSISTENCY_CHECK_PERIOD.";
        default sw = w;
        default onwrite = wzc;
        default hw = na;
        field {
            desc = "When cleared to 0, !!INTEGRITY_CHECK_PERIOD and !!CONSISTENCY_CHECK_PERIOD registers cannot be written anymore.\nWrite 0 to clear this bit.";
            reset = 0x1;
        } REGWEN [0:0];
    } CHECK_REGWEN @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        desc = "Timeout value for the integrity and consistency checks.";
        default sw = rw;
        default hw = r;
        default swwe = CHECK_REGWEN;
        field {
            desc = "Timeout value in cycles for the for the integrity and consistency checks. If an integrity or consistency
                    check does not complete within the timeout window, an error will be flagged in the !!STATUS register, 
                    an otp_error interrupt will be raised, and an fatal_check_error alert will be sent out. The timeout should 
                    be set to a large value to stay on the safe side. The maximum check time can be upper bounded by the 
                    number of cycles it takes to readout, scramble and digest the entire OTP array. Since this amounts to 
                    rughly 25k cycles, it is recommended to set this value to at least 100'000 cycles in order to stay on the 
                    safe side. A value of zer disables the timeout mechanism (default).";
            reset = 0x0;
        } TIMEOUT [31:0];
    } CHECK_TIMEOUT @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        desc = "This value specifies the maximum period that can be generated pseudo-randomly.\nOnly applies to the HW_CFG* and SECRET* partitions once they are locked.";
        default sw = rw;
        default hw = r;
        default swwe = CHECK_REGWEN;
        field {
            desc = "The pseudo-random period is generated using a 40bit LFSR internally, and this register defines 
            the bit mask to be applied to the LFSR output in order to limit its range. The value of this 
            register is left shifted by 8bits and the lower bits are set to 8'hFF in order to form the 40bit mask. 
            A recommended value is 0x3_FFFF, corresponding to a maximum period of ~2.8s at 24MHz. 
            A value of zer disables the timer (default). Note that a one-off check can always be triggered via 
            !!CHECK_TRIGGER.INTEGRITY.";
            reset = 0x0;
        } PERIOD [31:0];
    } INTEGRITY_CHECK_PERIOD @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        desc = "This value specifies the maximum period that can be generated pseudo-randomly.\nThis applies to the LIFE_CYCLE partition and the HW_CFG* and SECRET* partitions once they are locked.";
        default sw = rw;
        default hw = r;
        default swwe = CHECK_REGWEN;
        field {
            desc = "The pseudo-random period is generated using a 40bit LFSR internally, and this register defines\nthe bit mask to be applied to the LFSR output in order to limit its range. The value of this\nregister is left shifted by 8bits and the lower bits are set to 8'hFF in order to form the 40bit mask.\nA recommended value is 0x3FF_FFFF, corresponding to a maximum period of ~716s at 24MHz.\nA value of zer disables the timer (default). Note that a one-off check can always be triggered via\n!!CHECK_TRIGGER.CONSISTENCY.";
            reset = 0x0;
        } PERIOD [31:0];
    } CONSISTENCY_CHECK_PERIOD @ ${"0x%X" % + inc_ptr(0x4)};

% for partition in partitions:
  % if partition["read_lock"] == "CSR":
    reg {
    desc = "Runtime read lock for the ${partition["name"]} partition.";
        default sw = rw;
        default onwrite = wzc;
        default hw = r;
        default swwe = DIRECT_ACCESS_REGWEN;
        field {
            desc = "When cleared to 0, read access to the ${partition["name"]} partition is locked.\nWrite 0 to clear this bit.";
            reset = 0x1;
        } READ_LOCK [0:0];
    } ${partition["name"]}_READ_LOCK @${"0x%X" % + inc_ptr(0x4)};
  % endif
% endfor

    reg {
        desc = "Volatile write lock for vendor public key hashes.";
        default sw = rw;
        default hw = r;
        field {
            desc = "One-hot encoded";
            reset = 0x0;
        } PERIOD [31:0];
    } VENDOR_PK_HASH_VOLATILE_LOCK @ ${"0x%X" % + inc_ptr(0x4)};

    regfile digest_t {
        /* -----------------------------------
        * Default prperties for Register File
        * --------------------------------- */
        name = "DIGEST";
        desc = "Digest register block";
        default reset = 0x0;

        default sw = r;
        default hw = r;
        //default hwext = true;
        
        /* ------------------------------------
        * Register definitions
        * -----------------------------------*/
        reg digest_reg_t {
            name = "DIGEST";
            desc = "Integrity digest for partition. 
            The integrity digest is 0 by default. Software must write this 
            digest value via the direct access interface in order to lock the partition. 
            After a reset, write access to the VENDOR_TEST partition is locked and\n  the digest becomes visible in this CSR.";

            default sw = r; // field prperty
            default hw = w; // field prperty

            field { desc = "Digest.";} DIGEST [31:0];
        };

        /* ------------- Registers --------------*/
        digest_reg_t DIGEST_0 @ 0x0; //
        digest_reg_t DIGEST_1 @ 0x4; //  
        /* --------------------------------------*/
    };

% for i, partition in enumerate(partitions):
  % if partition["write_lock"] == "Digest":
    digest_t ${partition["name"]}_DIGEST @ ${"0x%X" % + inc_ptr(0x4 if i == 0 else 0x8)};
  % endif
% endfor

    reg {
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field0[0:0] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field1[1:1] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field2[2:2] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field3[13:4] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field4[26:16] = 0x0;
    } CSR0 @ ${"0x%X" % + inc_ptr(0x0)};

    reg {
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field0[6:0] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field1[7:7] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field2[14:8] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field3[15:15] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field4[31:16] = 0x0;
    } CSR1 @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field0[0:0] = 0x0;
    } CSR2 @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        field {
            desc = "";
            sw = rw;
            hw = rw;
        } field0[2:0] = 0x0;
        field {
            desc = "";
            sw = rw;
            onwrite = woclr;
            hw = rw;
        } field1[13:4] = 0x0;
        field {
            desc = "";
            sw = rw;
            onwrite = woclr;
            hw = rw;
        } field2[16:16] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field3[17:17] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field4[18:18] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field5[19:19] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field6[20:20] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field7[21:21] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field8[22:22] = 0x0;
    } CSR3 @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field0[9:0] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field1[12:12] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field2[13:13] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field3[14:14] = 0x0;
    } CSR4 @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        field {
            desc = "";
            sw = rw;
            hw = rw;
        } field0[5:0] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = rw;
        } field1[7:6] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field2[8] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field3[11:9] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field4[12] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field5[13] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = rw;
        } field6[31:16] = 0x0;
    } CSR5 @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        field {
            desc = "";
            sw = rw;
            hw = r;
        } field0[9:0] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = rw;
        } field1[11:11] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = rw;
        } field2[12:12] = 0x0;
        field {
            desc = "";
            sw = rw;
            hw = rw;
        } field3[31:16] = 0x0;
    } CSR6 @ ${"0x%X" % + inc_ptr(0x4)};

    reg {
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field0[5:0] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field1[10:8] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field2[14:14] = 0x0;
        field {
            desc = "";
            sw = r;
            hw = rw;
        } field3[15:15] = 0x0;
    } CSR7 @ ${"0x%X" % + inc_ptr(0x4)};
};