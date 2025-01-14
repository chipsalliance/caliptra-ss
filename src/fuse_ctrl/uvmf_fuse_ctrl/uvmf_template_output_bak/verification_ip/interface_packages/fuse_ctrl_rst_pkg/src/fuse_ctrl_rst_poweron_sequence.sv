//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This sequences randomizes the fuse_ctrl_rst transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a fuse_ctrl_rst_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class fuse_ctrl_rst_poweron_sequence extends duse_ctrl_rst_sequence_base;

    `uvm_object_utils( fuse_ctrl_rst_random_sequence )

    function new(string name = "");
        super.new(name);
    endfunction: new

    // ****************************************************************************
    // TASK : body()
    // This task is automatically executed when this sequence is started using the
    // start(sequencerHandle) task.
    //
    task body();

        // Initiate first transaction with rst_ni = 0 (asserted), pwr_otp_i = 0 (deasserted)
        req = fuse_ctrl_rst_transaction::type_id:: create("rst_req");
        start_item(req);
        // Randomize the transaction
        if (!req.randomize()) `uvm_fatal("FUSE_CTRL_RST_POWERON", "fuse_ctrl_rst_poweron_sequence::body()-fuse_ctrl_rst_transaction randomization failed")
        `uvm_info("FUSE_CTRL_RST_POWERON", "Asserting reset", UVM_MEDIUM)
        req.assert_rst = '1b0;
        req.assert_otp_init = 1'b0;
        finish_item(req);
        `uvm_info("FUSE_CTRL_RST_POWERON", {"Response:", req.convert2string()}, UVM_MEDIUM)

        // Deassert rst_ni, pwr_otp_i = 0 (deasserted)
        req = fuse_ctrl_rst_transaction::type_id:: create("rst_release_req");
        start_item(req);
        // Randomize the transaction
        if (!req.randomize()) `uvm_fatal("FUSE_CTRL_RST_POWERON", "fuse_ctrl_rst_poweron_sequence::body()-fuse_ctrl_rst_transaction randomization failed")
        `uvm_info("FUSE_CTRL_RST_POWERON", "Deasserting reset, reset phase done", UVM_MEDIUM)
        req.assert_rst = '1b1;
        req.assert_otp_init = 1'b0;
        finish_item(req);
        `uvm_info("FUSE_CTRL_RST_POWERON", {"Response:", req.convert2string()}, UVM_MEDIUM)

        // Assert pwr_otp_i = 1
        req = fuse_ctrl_rst_transaction::type_id:: create("otp_init_req");
        start_item(req);
        // Randomize the transaction
        if (!req.randomize()) `uvm_fatal("FUSE_CTRL_RST_POWERON", "fuse_ctrl_rst_poweron_sequence::body()-fuse_ctrl_rst_transaction randomization failed")
        `uvm_info("FUSE_CTRL_RST_POWERON", "Asserting init request to all partitions", UVM_MEDIUM)
        req.assert_rst = 1'b1;
        req.assert_otp_init = 1'b1;
        finish_item(req);
        `uvm_info("FUSE_CTRL_RST_POWERON", {"Response:", req.convert2string()}, UVM_MEDIUM)

    endtask

endclass