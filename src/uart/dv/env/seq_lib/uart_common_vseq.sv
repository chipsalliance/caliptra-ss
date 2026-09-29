// Copyright 2026 Google LLC (chipsalliance project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_common_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    if ($test$plusargs("run_sec_cm_fi") || $test$plusargs("run_sec_cm")) begin
      uart_sec_cm_vseq sec_cm_vseq;
      `uvm_create_on(sec_cm_vseq, p_sequencer)
      `DV_CHECK_RANDOMIZE_FATAL(sec_cm_vseq)
      sec_cm_vseq.start(p_sequencer);
    end

  endtask : body

endclass
