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
// DESCRIPTION: This class records fuse_ctrl_prim_axi_write_in transaction information using
//       a covergroup named fuse_ctrl_prim_axi_write_in_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class fuse_ctrl_prim_axi_write_in_transaction_coverage #(
      int AW = 32,
      int DW = 32,
      int IW = 3,
      int UW = 32
      )
 extends uvm_subscriber #(.T(fuse_ctrl_prim_axi_write_in_transaction #(
                                            .AW(AW),
                                            .DW(DW),
                                            .IW(IW),
                                            .UW(UW)
                                            )
));

  `uvm_component_param_utils( fuse_ctrl_prim_axi_write_in_transaction_coverage #(
                              AW,
                              DW,
                              IW,
                              UW
                              )
)

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup fuse_ctrl_prim_axi_write_in_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    prim_awaddr: coverpoint coverage_trans.prim_awaddr;
    prim_awvalid: coverpoint coverage_trans.prim_awvalid;
    prim_awburst: coverpoint coverage_trans.prim_awburst;
    prim_awsize: coverpoint coverage_trans.prim_awsize;
    prim_awlen: coverpoint coverage_trans.prim_awlen;
    prim_awuser: coverpoint coverage_trans.prim_awuser;
    prim_awid: coverpoint coverage_trans.prim_awid;
    prim_awlock: coverpoint coverage_trans.prim_awlock;
    prim_wdata: coverpoint coverage_trans.prim_wdata;
    prim_wstrb: coverpoint coverage_trans.prim_wstrb;
    prim_wvalid: coverpoint coverage_trans.prim_wvalid;
    prim_wlast: coverpoint coverage_trans.prim_wlast;
    prim_bready: coverpoint coverage_trans.prim_bready;
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    fuse_ctrl_prim_axi_write_in_transaction_cg=new;
    `uvm_warning("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that transaction variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this warning after the covergroup has been reviewed.")
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    fuse_ctrl_prim_axi_write_in_transaction_cg.set_inst_name($sformatf("fuse_ctrl_prim_axi_write_in_transaction_cg_%s",get_full_name()));
  endfunction

  // ****************************************************************************
  // FUNCTION: write (T t)
  // This function is automatically executed when a transaction arrives on the
  // analysis_export.  It copies values from the variables in the transaction 
  // to local variables used to collect functional coverage.  
  //
  virtual function void write (T t);
    `uvm_info("COV","Received transaction",UVM_HIGH);
    coverage_trans = t;
    fuse_ctrl_prim_axi_write_in_transaction_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
