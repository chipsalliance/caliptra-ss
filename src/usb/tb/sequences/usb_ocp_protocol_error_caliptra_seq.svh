// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_protocol_error_caliptra_seq extends usb_ocp_base_caliptra_seq;
  `uvm_object_utils(usb_ocp_protocol_error_caliptra_seq)
  usb_ocp_protocol_error_model error_model;

  function new(string name = "usb_ocp_protocol_error_caliptra_seq");
    super.new(name);
  endfunction

  virtual task ocp_do_check_dma_boundary();
    time deadline;
    deadline = $time + ocp_cfg.control_transfer_timeout;
    while (!error_model.release_dma) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_ERROR_DMA", "Error experiment did not release normal DMA")
      #1us;
    end
  endtask

  task ocp_do_snapshots();
    logic [31:0] data;
    string names[6] = '{"DEVICE_STATUS_0","INDIRECT_FIFO_CTRL_0",
      "INDIRECT_FIFO_CTRL_1","INDIRECT_FIFO_STATUS_0",
      "INDIRECT_FIFO_STATUS_1","INDIRECT_FIFO_STATUS_2"};
    while (!ocp_cfg.stop_requested) begin
      fork
        begin
          fork
            wait (error_model.snapshot_requested);
            wait (ocp_cfg.stop_requested);
          join_any
          disable fork;
        end
      join
      if (ocp_cfg.stop_requested) return;
      error_model.snapshot_requested = 0;
      foreach (names[i]) begin
        ocp_read_register(names[i],data);
        error_model.snapshot[names[i]] = data;
      end
      if (error_model.sample_setup_debug) begin
        ocp_read_register("CALIPTRA_SETUP_DEBUG",data);
        error_model.snapshot["CALIPTRA_SETUP_DEBUG"] = data;
      end
      error_model.snapshot_complete = 1;
    end
  endtask

  task body();
    if (error_model == null)
      `uvm_fatal("OCP_ERROR_GUARD", "Missing error experiment for firmware actor")
    fork
      super.body();
      ocp_do_snapshots();
    join
  endtask
endclass
