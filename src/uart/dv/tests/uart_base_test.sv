// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class axi_putrsp_catcher extends uvm_report_catcher;
  `uvm_object_utils(axi_putrsp_catcher)
  function new(string name = "axi_putrsp_catcher");
    super.new(name);
  endfunction
  virtual function action_e catch();
    if (get_severity() == UVM_FATAL && get_id() == "PUTRSP") begin
      set_severity(UVM_INFO);
      return CAUGHT;
    end
    return THROW;
  endfunction
endclass

class uart_base_test extends dv_base_test #(.ENV_T(uart_env), .CFG_T(uart_env_cfg));
  `uvm_component_utils(uart_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    axi_putrsp_catcher putrsp_catcher;
    max_quit_count  = 50;
    test_timeout_ns = 64'd10_000_000_000; // 10s
    super.build_phase(phase);
    putrsp_catcher = axi_putrsp_catcher::type_id::create("putrsp_catcher");
    uvm_report_cb::add(null, putrsp_catcher);
  endfunction : build_phase

endclass : uart_base_test
