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
// This sequences randomizes the fuse_ctrl_in transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a fuse_ctrl_in_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class fuse_ctrl_in_random_sequence #(
      int AlertSyncOn = 3,
      caliptra_otp_ctrl_pkg::lfsr_seed_t RndConstLfrSeed = caliptra_otp_ctrl_pkg::RndCnstLfsrSeedDefault,
      caliptra_otp_ctrl_pkg::lfsr_perm_t RndCnstLfsrPerm = caliptra_otp_ctrl_pkg::RndCnstLfsrPermDefault,
      string MemInitFile = "/home/ws/caliptra/anjpar/ws1/chipsalliance/caliptra-rtl/src/fuse_ctrl/data/otp-img.2048.vmem"
      )

  extends fuse_ctrl_in_sequence_base #(
      .AlertSyncOn(AlertSyncOn),
      .RndConstLfrSeed(RndConstLfrSeed),
      .RndCnstLfsrPerm(RndCnstLfsrPerm),
      .MemInitFile(MemInitFile)
      )
;

  `uvm_object_param_utils( fuse_ctrl_in_random_sequence #(
                           AlertSyncOn,
                           RndConstLfrSeed,
                           RndCnstLfsrPerm,
                           MemInitFile
                           )
)

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  //*****************************************************************
  function new(string name = "");
    super.new(name);
  endfunction: new

  // ****************************************************************************
  // TASK : body()
  // This task is automatically executed when this sequence is started using the 
  // start(sequencerHandle) task.
  //
  task body();
  
      // Construct the transaction
      req=fuse_ctrl_in_transaction#(
                .AlertSyncOn(AlertSyncOn),
                .RndConstLfrSeed(RndConstLfrSeed),
                .RndCnstLfsrPerm(RndCnstLfsrPerm),
                .MemInitFile(MemInitFile)
                )
::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "fuse_ctrl_in_random_sequence::body()-fuse_ctrl_in_transaction randomization failed")
      // Send the transaction to the fuse_ctrl_in_driver_bfm via the sequencer and fuse_ctrl_in_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: fuse_ctrl_in_random_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end
