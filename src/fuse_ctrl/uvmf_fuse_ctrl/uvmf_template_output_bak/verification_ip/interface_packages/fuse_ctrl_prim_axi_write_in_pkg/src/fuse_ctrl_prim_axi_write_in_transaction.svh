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
// DESCRIPTION: This class defines the variables required for an fuse_ctrl_prim_axi_write_in
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class fuse_ctrl_prim_axi_write_in_transaction #(
      int AW = 32,
      int DW = 32,
      int IW = 3,
      int UW = 32
      )
 extends uvmf_transaction_base;

  `uvm_object_param_utils( fuse_ctrl_prim_axi_write_in_transaction #(
                           AW,
                           DW,
                           IW,
                           UW
                           )
)

  rand logic [AW-1:0] prim_awaddr ;
  logic prim_awvalid ;
  logic [$bits(axi_pkg::axi_burst_e)] prim_awburst ;
  logic [2:0] prim_awsize ;
  logic [7:0] prim_awlen ;
  logic [UW-1:0] prim_awuser ;
  logic [IW-1:0] prim_awid ;
  logic prim_awlock ;
  logic [DW-1:0] prim_wdata ;
  logic [DW/8 - 1:0] prim_wstrb ;
  logic prim_wvalid ;
  logic prim_wlast ;
  logic prim_bready ;

  //Constraints for the transaction variables:

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in fuse_ctrl_prim_axi_write_in_macros.svh

  //*******************************************************************
  // Monitor macro used by fuse_ctrl_prim_axi_write_in_monitor and fuse_ctrl_prim_axi_write_in_monitor_bfm
  // This struct is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_MONITOR_STRUCT
    fuse_ctrl_prim_axi_write_in_monitor_s fuse_ctrl_prim_axi_write_in_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a fuse_ctrl_prim_axi_write_in_monitor_s
  // structure.  The function returns the handle to the fuse_ctrl_prim_axi_write_in_monitor_struct.
  // This function is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by fuse_ctrl_prim_axi_write_in_driver and fuse_ctrl_prim_axi_write_in_driver_bfm
  // to communicate initiator driven data to fuse_ctrl_prim_axi_write_in_driver_bfm.
  // This struct is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_INITIATOR_STRUCT
    fuse_ctrl_prim_axi_write_in_initiator_s fuse_ctrl_prim_axi_write_in_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a fuse_ctrl_prim_axi_write_in_initiator_s
  // structure.  The function returns the handle to the fuse_ctrl_prim_axi_write_in_initiator_struct.
  // This function is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by fuse_ctrl_prim_axi_write_in_driver and fuse_ctrl_prim_axi_write_in_driver_bfm
  // to communicate Responder driven data to fuse_ctrl_prim_axi_write_in_driver_bfm.
  // This struct is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_RESPONDER_STRUCT
    fuse_ctrl_prim_axi_write_in_responder_s fuse_ctrl_prim_axi_write_in_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a fuse_ctrl_prim_axi_write_in_responder_s
  // structure.  The function returns the handle to the fuse_ctrl_prim_axi_write_in_responder_struct.
  // This function is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in fuse_ctrl_prim_axi_write_in_macros.svh
  `fuse_ctrl_prim_axi_write_in_FROM_RESPONDER_STRUCT_FUNCTION 
  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new( string name = "" );
    super.new( name );
  endfunction

  // ****************************************************************************
  // FUNCTION: convert2string()
  // This function converts all variables in this class to a single string for 
  // logfile reporting.
  //
  virtual function string convert2string();
    // pragma uvmf custom convert2string begin
    // UVMF_CHANGE_ME : Customize format if desired.
    return $sformatf("prim_awaddr:0x%x prim_awvalid:0x%x prim_awburst:0x%x prim_awsize:0x%x prim_awlen:0x%x prim_awuser:0x%x prim_awid:0x%x prim_awlock:0x%x prim_wdata:0x%x prim_wstrb:0x%x prim_wvalid:0x%x prim_wlast:0x%x prim_bready:0x%x ",prim_awaddr,prim_awvalid,prim_awburst,prim_awsize,prim_awlen,prim_awuser,prim_awid,prim_awlock,prim_wdata,prim_wstrb,prim_wvalid,prim_wlast,prim_bready);
    // pragma uvmf custom convert2string end
  endfunction

  //*******************************************************************
  // FUNCTION: do_print()
  // This function is automatically called when the .print() function
  // is called on this class.
  //
  virtual function void do_print(uvm_printer printer);
    // pragma uvmf custom do_print begin
    // UVMF_CHANGE_ME : Current contents of do_print allows for the use of UVM 1.1d, 1.2 or P1800.2.
    // Update based on your own printing preference according to your preferred UVM version
    $display(convert2string());
    // pragma uvmf custom do_print end
  endfunction

  //*******************************************************************
  // FUNCTION: do_compare()
  // This function is automatically called when the .compare() function
  // is called on this class.
  //
  virtual function bit do_compare (uvm_object rhs, uvm_comparer comparer);
    fuse_ctrl_prim_axi_write_in_transaction #(
        .AW(AW),
        .DW(DW),
        .IW(IW),
        .UW(UW)
        )
 RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.prim_wdata == RHS.prim_wdata)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    fuse_ctrl_prim_axi_write_in_transaction #(
        .AW(AW),
        .DW(DW),
        .IW(IW),
        .UW(UW)
        )
 RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.prim_awaddr = RHS.prim_awaddr;
    this.prim_awvalid = RHS.prim_awvalid;
    this.prim_awburst = RHS.prim_awburst;
    this.prim_awsize = RHS.prim_awsize;
    this.prim_awlen = RHS.prim_awlen;
    this.prim_awuser = RHS.prim_awuser;
    this.prim_awid = RHS.prim_awid;
    this.prim_awlock = RHS.prim_awlock;
    this.prim_wdata = RHS.prim_wdata;
    this.prim_wstrb = RHS.prim_wstrb;
    this.prim_wvalid = RHS.prim_wvalid;
    this.prim_wlast = RHS.prim_wlast;
    this.prim_bready = RHS.prim_bready;
    // pragma uvmf custom do_copy end
  endfunction

  // ****************************************************************************
  // FUNCTION: add_to_wave()
  // This function is used to display variables in this class in the waveform 
  // viewer.  The start_time and end_time variables must be set before this 
  // function is called.  If the start_time and end_time variables are not set
  // the transaction will be hidden at 0ns on the waveform display.
  // 
  virtual function void add_to_wave(int transaction_viewing_stream_h);
    `ifdef QUESTA
    if (transaction_view_h == 0) begin
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"fuse_ctrl_prim_axi_write_in_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,prim_awaddr,"prim_awaddr");
    $add_attribute(transaction_view_h,prim_awvalid,"prim_awvalid");
    $add_attribute(transaction_view_h,prim_awburst,"prim_awburst");
    $add_attribute(transaction_view_h,prim_awsize,"prim_awsize");
    $add_attribute(transaction_view_h,prim_awlen,"prim_awlen");
    $add_attribute(transaction_view_h,prim_awuser,"prim_awuser");
    $add_attribute(transaction_view_h,prim_awid,"prim_awid");
    $add_attribute(transaction_view_h,prim_awlock,"prim_awlock");
    $add_attribute(transaction_view_h,prim_wdata,"prim_wdata");
    $add_attribute(transaction_view_h,prim_wstrb,"prim_wstrb");
    $add_attribute(transaction_view_h,prim_wvalid,"prim_wvalid");
    $add_attribute(transaction_view_h,prim_wlast,"prim_wlast");
    $add_attribute(transaction_view_h,prim_bready,"prim_bready");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
