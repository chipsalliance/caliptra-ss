// Copyright 2026 Google LLC (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Scoped, count-bounded report catcher for expected UVM RAL advisories (Comment #14):
// 1) Sub-field polling in csr_spinwait/csr_rd reads 1-bit/narrow fields in STATUS, CONTROL,
//    ERROR_STATUS, or CONFIGOPTS across a 32-bit word-aligned register bus ("RegModel").
// 2) Only when +run_same_csr_outstanding intentionally issues back-to-back non-blocking writes
//    to the same CSR, UVM/FLD/SET/BSY is expected within a bounded count; in all other tests,
//    UVM/FLD/SET/BSY remains unsuppressed so accidental busy-field races are caught.
class spi_host_scoped_ral_catcher extends uvm_report_catcher;
  `uvm_object_utils(spi_host_scoped_ral_catcher)

  localparam int unsigned MAX_REGMODEL_FIELD_ADVISORIES = 500000;
  localparam int unsigned MAX_SAME_CSR_BSY_WARNINGS     = 2000;

  int unsigned caught_regmodel_cnt = 0;
  int unsigned caught_fld_bsy_cnt  = 0;
  bit          allow_same_csr_bsy  = 1'b0;

  function new(string name = "spi_host_scoped_ral_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    string id  = get_id();
    string msg = get_message();
    if (get_severity() == UVM_WARNING && id == "RegModel" &&
        uvm_is_match("*Individual field access not available for field 'spi_host_reg_block.*", msg)) begin
      caught_regmodel_cnt++;
      if (caught_regmodel_cnt <= MAX_REGMODEL_FIELD_ADVISORIES) begin
        return CAUGHT;
      end
    end else if (allow_same_csr_bsy && get_severity() == UVM_WARNING && id == "UVM/FLD/SET/BSY" &&
                 uvm_is_match("*spi_host_reg_block.*", msg)) begin
      caught_fld_bsy_cnt++;
      if (caught_fld_bsy_cnt <= MAX_SAME_CSR_BSY_WARNINGS) begin
        return CAUGHT;
      end
    end
    return THROW;
  endfunction
endclass : spi_host_scoped_ral_catcher

class spi_host_base_test extends dv_base_test #(
    .CFG_T(spi_host_env_cfg),
    .ENV_T(spi_host_env)
  );

  `uvm_component_utils(spi_host_base_test)
  `uvm_component_new

  spi_host_scoped_ral_catcher m_scoped_ral_catcher;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_scoped_ral_catcher = spi_host_scoped_ral_catcher::type_id::create("m_scoped_ral_catcher");
    m_scoped_ral_catcher.allow_same_csr_bsy = $test$plusargs("run_same_csr_outstanding");
    uvm_report_cb::add(null, m_scoped_ral_catcher);
  endfunction : build_phase

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    if (uvm_top.get_report_verbosity_level() > UVM_LOW) begin
      uvm_top.print_topology();
    end
  endfunction // end_of_elaboration

  virtual task run_phase(uvm_phase phase);
    fork
      super.run_phase(phase);
      if (cfg.is_active) begin
        env.run_layered_register_vseq();
      end
    join
  endtask

  virtual function void report_phase(uvm_phase phase);
    if (m_scoped_ral_catcher != null) begin
      `DV_CHECK_LE(m_scoped_ral_catcher.caught_regmodel_cnt,
                   spi_host_scoped_ral_catcher::MAX_REGMODEL_FIELD_ADVISORIES,
                   "Scoped RegModel field-access advisory count exceeded bound")
      `DV_CHECK_LE(m_scoped_ral_catcher.caught_fld_bsy_cnt,
                   spi_host_scoped_ral_catcher::MAX_SAME_CSR_BSY_WARNINGS,
                   "Scoped same_csr_outstanding UVM/FLD/SET/BSY count exceeded bound")
    end
    super.report_phase(phase);
  endfunction : report_phase
endclass : spi_host_base_test
