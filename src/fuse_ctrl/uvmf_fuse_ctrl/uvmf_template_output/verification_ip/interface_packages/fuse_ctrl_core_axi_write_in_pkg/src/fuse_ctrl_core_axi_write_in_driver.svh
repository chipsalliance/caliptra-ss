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
// DESCRIPTION: This class passes transactions between the sequencer
//        and the BFM driver interface.  It accesses the driver BFM 
//        through the bfm handle. This driver
//        passes transactions to the driver BFM through the access
//        task.  
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class fuse_ctrl_core_axi_write_in_driver  #(
      int AW = 32,
      int DW = 32,
      int IW = 3,
      int UW = 32
      ) extends uvmf_driver_base #(
                   .CONFIG_T(fuse_ctrl_core_axi_write_in_configuration  #(
                             .AW(AW),
                             .DW(DW),
                             .IW(IW),
                             .UW(UW)
                             ) ),
                   .BFM_BIND_T(virtual fuse_ctrl_core_axi_write_in_driver_bfm  #(
                             .AW(AW),
                             .DW(DW),
                             .IW(IW),
                             .UW(UW)
                             ) ),
                   .REQ(fuse_ctrl_core_axi_write_in_transaction  #(
                             .AW(AW),
                             .DW(DW),
                             .IW(IW),
                             .UW(UW)
                             ) ),
                   .RSP(fuse_ctrl_core_axi_write_in_transaction  #(
                             .AW(AW),
                             .DW(DW),
                             .IW(IW),
                             .UW(UW)
                             ) ));

  `uvm_component_param_utils( fuse_ctrl_core_axi_write_in_driver #(
                              AW,
                              DW,
                              IW,
                              UW
                              ))
//*******************************************************************
// Macros that define structs located in fuse_ctrl_core_axi_write_in_macros.svh
//*******************************************************************
// Initiator macro used by fuse_ctrl_core_axi_write_in_driver and fuse_ctrl_core_axi_write_in_driver_bfm
// to communicate initiator driven data to fuse_ctrl_core_axi_write_in_driver_bfm.           
`fuse_ctrl_core_axi_write_in_INITIATOR_STRUCT
  fuse_ctrl_core_axi_write_in_initiator_s fuse_ctrl_core_axi_write_in_initiator_struct;
//*******************************************************************
// Responder macro used by fuse_ctrl_core_axi_write_in_driver and fuse_ctrl_core_axi_write_in_driver_bfm
// to communicate Responder driven data to fuse_ctrl_core_axi_write_in_driver_bfm.
`fuse_ctrl_core_axi_write_in_RESPONDER_STRUCT
  fuse_ctrl_core_axi_write_in_responder_s fuse_ctrl_core_axi_write_in_responder_struct;

// pragma uvmf custom class_item_additional begin
// pragma uvmf custom class_item_additional end

// ****************************************************************************
// This function is the standard SystemVerilog constructor.
//
  function new( string name = "", uvm_component parent=null );
    super.new( name, parent );
  endfunction

// ****************************************************************************
// This function sends configuration object variables to the driver BFM 
// using the configuration struct.
//
  virtual function void configure(input CONFIG_T cfg);
      bfm.configure( cfg.to_struct() );
  endfunction

// ****************************************************************************
// This function places a handle to this class in the proxy variable in the
// driver BFM.  This allows the driver BFM to call tasks and function within this class.
//
  virtual function void set_bfm_proxy_handle();
    bfm.proxy = this;  endfunction

// **************************************************************************** 
// This task is called by the run_phase in uvmf_driver_base.              
  virtual task access( inout REQ txn );
// pragma uvmf custom access begin
    if (configuration.initiator_responder==RESPONDER) begin
      // Complete current transfer and wait for next transfer
      bfm.respond_and_wait_for_next_transfer( 
          fuse_ctrl_core_axi_write_in_initiator_struct, 
          txn.to_responder_struct() 
          );
      // Unpack information about initiated transfer received by this responder
      txn.from_initiator_struct(fuse_ctrl_core_axi_write_in_initiator_struct);
    end else begin    
      // Initiate a transfer and get response
      bfm.initiate_and_get_response( 
          txn.to_initiator_struct(), 
          fuse_ctrl_core_axi_write_in_responder_struct 
          );
      // Unpack transfer response information received by this initiator
      txn.from_responder_struct(fuse_ctrl_core_axi_write_in_responder_struct);
    end
// pragma uvmf custom access end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

