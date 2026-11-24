// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

class usb_ocp_protocol_error_host_seq extends usb_ocp_base_host_seq;
  `uvm_object_utils(usb_ocp_protocol_error_host_seq)
  usb_ocp_scoreboard scoreboard;
  usb_ocp_protocol_error_model error_model;

  function new(string name = "usb_ocp_protocol_error_host_seq");
    super.new(name);
  endfunction

  task ocp_poll_observation();
    time deadline;
    deadline = $time + ocp_cfg.control_transfer_timeout;
    while (scoreboard.busy || !observer.ocp_check_snapshots_consumed() ||
           scoreboard.model.ready_controls.size() != 0) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_ERROR_OBSERVATION", "Ordered observer did not retire the error experiment")
      #1ns;
    end
  endtask

  task ocp_do_check_snapshot();
    time deadline;
    deadline = $time + ocp_cfg.control_transfer_timeout;
    if (error_model.snapshot_requested)
      `uvm_fatal("OCP_ERROR_SNAPSHOT", "Overlapping firmware snapshot requests")
    error_model.snapshot_complete = 0;
    error_model.snapshot_requested = 1;
    while (!error_model.snapshot_complete) begin
      if ($time >= deadline)
        `uvm_fatal("OCP_ERROR_SNAPSHOT", "Frontdoor firmware snapshot timed out")
      #1ns;
    end
    ocp_poll_observation();
  endtask

  task ocp_check_snapshot_unchanged(logic [31:0] ctrl, logic [31:0] words,
      logic [31:0] flags, logic [31:0] wr, logic [31:0] rd);
    if (error_model.snapshot["INDIRECT_FIFO_CTRL_0"] !== ctrl ||
        error_model.snapshot["INDIRECT_FIFO_CTRL_1"] !== words ||
        error_model.snapshot["INDIRECT_FIFO_STATUS_0"] !== flags ||
        error_model.snapshot["INDIRECT_FIFO_STATUS_1"] !== wr ||
        error_model.snapshot["INDIRECT_FIFO_STATUS_2"] !== rd)
      `uvm_fatal("OCP_ERROR_COMMIT", $sformatf(
        "Rejected DATA changed FIFO/control state: snapshot=%p",error_model.snapshot))
  endtask

  // The first DEVICE_STATUS SETUP also clears any protocol STALL (USB 2.0 8.5.3.4);
  // the completed Recovery Agent read clears the error code (OCP 1.1 9.2).
  task ocp_do_check_error_status();
    bytes_t response;
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,response);
    ocp_do_check_read(OCP_CMD_DEVICE_STATUS,response);
    ocp_poll_observation();
    error_model.finished = 1;
    error_model.ocp_check_complete();
  endtask

  virtual function void ocp_check_stall_result(usb_ocp_event observed);
    if (!error_model.native_checked || observed.vendor_instance != error_model.native_instance ||
        observed.setup !== error_model.setup || observed.transfer_ok !== 0)
      `uvm_fatal("OCP_ERROR_NATIVE", "Host consumed an unowned STALL completion")
  endfunction

  virtual task ocp_do_check_host_completion();
    if (error_model.armed) error_model.ocp_check_complete();
  endtask

  task body();
    if (scoreboard == null || error_model == null ||
        scoreboard.model.error_model != error_model)
      `uvm_fatal("OCP_ERROR_GUARD", "Host and checker do not share the experiment")
    ocp_cfg.control_transfer_timeout = 500us;
    recovery_status_timeout = 5ms;
    super.body();
  endtask
endclass
