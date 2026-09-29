// Copyright 2026 Google LLC  (chipsalliance project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The configuration for an agent driving/monitoring the interfaces for AXI (AW, W, B, AR, R)

class axi_agent_cfg extends uvm_object;
  `uvm_object_utils(axi_agent_cfg)

  bit en_cov    = 1'b1;
  bit en_assert = 1'b1;

  // Configurable ID width limit for register-layer sequences (default 8 bits -> m_id < 256)
  int unsigned reg_layer_id_width = 8;

  // Encode byte_mask[3:0] into AxUSER[21:18] in register-layer sequences (default enabled for Caliptra)
  bit en_caliptra_user_strb = 1'b1;

  virtual axi_write_request_if  write_request_vif;
  virtual axi_write_data_if     write_data_vif;
  virtual axi_write_response_if write_response_vif;
  virtual axi_read_request_if   read_request_vif;
  virtual axi_read_data_if      read_data_vif;

  function new(string name = "axi_agent_cfg");
    super.new(name);
  endfunction
endclass
