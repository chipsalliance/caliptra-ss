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
// DESCRIPTION: This analysis component contains analysis_exports for receiving
//   data and analysis_ports for sending data.
// 
//   This analysis component has the following analysis_exports that receive the 
//   listed transaction type.
//   
//   fuse_ctrl_rst_in_agent_ae receives transactions of type  fuse_ctrl_rst_in_transaction  
//   fuse_ctrl_core_axi_write_in_agent_ae receives transactions of type  fuse_ctrl_core_axi_write_in_transaction  
//   fuse_ctrl_prim_axi_write_in_agent_ae receives transactions of type  fuse_ctrl_prim_axi_write_in_transaction  
//   fuse_ctrl_core_axi_read_in_agent_ae receives transactions of type  fuse_ctrl_core_axi_read_in_transaction  
//   fuse_ctrl_prim_axi_read_in_agent_ae receives transactions of type  fuse_ctrl_prim_axi_read_in_transaction  
//   fuse_ctrl_secreg_axi_read_in_agent_ae receives transactions of type  fuse_ctrl_secreg_axi_read_in_transaction  
//   fuse_ctrl_lc_otp_in_agent_ae receives transactions of type  fuse_ctrl_lc_otp_in_transaction  
//   fuse_ctrl_in_agent_ae receives transactions of type  fuse_ctrl_in_transaction  
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//


class fuse_ctrl_scoreboard #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( fuse_ctrl_scoreboard #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_fuse_ctrl_rst_in_agent_ae #(fuse_ctrl_rst_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_rst_in_agent_ae;
  uvm_analysis_imp_fuse_ctrl_core_axi_write_in_agent_ae #(fuse_ctrl_core_axi_write_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_core_axi_write_in_agent_ae;
  uvm_analysis_imp_fuse_ctrl_prim_axi_write_in_agent_ae #(fuse_ctrl_prim_axi_write_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_prim_axi_write_in_agent_ae;
  uvm_analysis_imp_fuse_ctrl_core_axi_read_in_agent_ae #(fuse_ctrl_core_axi_read_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_core_axi_read_in_agent_ae;
  uvm_analysis_imp_fuse_ctrl_prim_axi_read_in_agent_ae #(fuse_ctrl_prim_axi_read_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_prim_axi_read_in_agent_ae;
  uvm_analysis_imp_fuse_ctrl_secreg_axi_read_in_agent_ae #(fuse_ctrl_secreg_axi_read_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_secreg_axi_read_in_agent_ae;
  uvm_analysis_imp_fuse_ctrl_lc_otp_in_agent_ae #(fuse_ctrl_lc_otp_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_lc_otp_in_agent_ae;
  uvm_analysis_imp_fuse_ctrl_in_agent_ae #(fuse_ctrl_in_transaction, fuse_ctrl_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) fuse_ctrl_in_agent_ae;




  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    fuse_ctrl_rst_in_agent_ae = new("fuse_ctrl_rst_in_agent_ae", this);
    fuse_ctrl_core_axi_write_in_agent_ae = new("fuse_ctrl_core_axi_write_in_agent_ae", this);
    fuse_ctrl_prim_axi_write_in_agent_ae = new("fuse_ctrl_prim_axi_write_in_agent_ae", this);
    fuse_ctrl_core_axi_read_in_agent_ae = new("fuse_ctrl_core_axi_read_in_agent_ae", this);
    fuse_ctrl_prim_axi_read_in_agent_ae = new("fuse_ctrl_prim_axi_read_in_agent_ae", this);
    fuse_ctrl_secreg_axi_read_in_agent_ae = new("fuse_ctrl_secreg_axi_read_in_agent_ae", this);
    fuse_ctrl_lc_otp_in_agent_ae = new("fuse_ctrl_lc_otp_in_agent_ae", this);
    fuse_ctrl_in_agent_ae = new("fuse_ctrl_in_agent_ae", this);
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_fuse_ctrl_rst_in_agent_ae
  // Transactions received through fuse_ctrl_rst_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_rst_in_agent_ae(fuse_ctrl_rst_in_transaction t);
    // pragma uvmf custom fuse_ctrl_rst_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_rst_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_rst_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_rst_in_agent_ae_scoreboard end
  endfunction

  // FUNCTION: write_fuse_ctrl_core_axi_write_in_agent_ae
  // Transactions received through fuse_ctrl_core_axi_write_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_core_axi_write_in_agent_ae(fuse_ctrl_core_axi_write_in_transaction t);
    // pragma uvmf custom fuse_ctrl_core_axi_write_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_core_axi_write_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_core_axi_write_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_core_axi_write_in_agent_ae_scoreboard end
  endfunction

  // FUNCTION: write_fuse_ctrl_prim_axi_write_in_agent_ae
  // Transactions received through fuse_ctrl_prim_axi_write_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_prim_axi_write_in_agent_ae(fuse_ctrl_prim_axi_write_in_transaction t);
    // pragma uvmf custom fuse_ctrl_prim_axi_write_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_prim_axi_write_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_prim_axi_write_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_prim_axi_write_in_agent_ae_scoreboard end
  endfunction

  // FUNCTION: write_fuse_ctrl_core_axi_read_in_agent_ae
  // Transactions received through fuse_ctrl_core_axi_read_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_core_axi_read_in_agent_ae(fuse_ctrl_core_axi_read_in_transaction t);
    // pragma uvmf custom fuse_ctrl_core_axi_read_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_core_axi_read_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_core_axi_read_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_core_axi_read_in_agent_ae_scoreboard end
  endfunction

  // FUNCTION: write_fuse_ctrl_prim_axi_read_in_agent_ae
  // Transactions received through fuse_ctrl_prim_axi_read_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_prim_axi_read_in_agent_ae(fuse_ctrl_prim_axi_read_in_transaction t);
    // pragma uvmf custom fuse_ctrl_prim_axi_read_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_prim_axi_read_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_prim_axi_read_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_prim_axi_read_in_agent_ae_scoreboard end
  endfunction

  // FUNCTION: write_fuse_ctrl_secreg_axi_read_in_agent_ae
  // Transactions received through fuse_ctrl_secreg_axi_read_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_secreg_axi_read_in_agent_ae(fuse_ctrl_secreg_axi_read_in_transaction t);
    // pragma uvmf custom fuse_ctrl_secreg_axi_read_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_secreg_axi_read_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_secreg_axi_read_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_secreg_axi_read_in_agent_ae_scoreboard end
  endfunction

  // FUNCTION: write_fuse_ctrl_lc_otp_in_agent_ae
  // Transactions received through fuse_ctrl_lc_otp_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_lc_otp_in_agent_ae(fuse_ctrl_lc_otp_in_transaction t);
    // pragma uvmf custom fuse_ctrl_lc_otp_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_lc_otp_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_lc_otp_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_lc_otp_in_agent_ae_scoreboard end
  endfunction

  // FUNCTION: write_fuse_ctrl_in_agent_ae
  // Transactions received through fuse_ctrl_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_fuse_ctrl_in_agent_ae(fuse_ctrl_in_transaction t);
    // pragma uvmf custom fuse_ctrl_in_agent_ae_scoreboard begin
    `uvm_info("PRED", "Transaction Received through fuse_ctrl_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    //  UVMF_CHANGE_ME: Implement custom scoreboard here.  
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The fuse_ctrl_scoreboard::write_fuse_ctrl_in_agent_ae function needs to be completed with custom scoreboard functionality",UVM_NONE)
    `uvm_info("UNIMPLEMENTED_CUSTOM_SCOREBOARD", "******************************************************************************************************",UVM_NONE)
 
    // pragma uvmf custom fuse_ctrl_in_agent_ae_scoreboard end
  endfunction



  // FUNCTION: extract_phase
  virtual function void extract_phase(uvm_phase phase);
// pragma uvmf custom extract_phase begin
     super.extract_phase(phase);
// pragma uvmf custom extract_phase end
  endfunction

  // FUNCTION: check_phase
  virtual function void check_phase(uvm_phase phase);
// pragma uvmf custom check_phase begin
     super.check_phase(phase);
// pragma uvmf custom check_phase end
  endfunction

  // FUNCTION: report_phase
  virtual function void report_phase(uvm_phase phase);
// pragma uvmf custom report_phase begin
     super.report_phase(phase);
// pragma uvmf custom report_phase end
  endfunction

endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

