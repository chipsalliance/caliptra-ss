// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// you may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Provides common construction, timeout, completion, and final pass/fail
// reporting for standalone USB UVM tests. Derived tests must set
// scenario_completed only after all scenario-specific checking has finished.
class usb_base_test extends uvm_test;
  `uvm_component_utils(usb_base_test)

  usb_env env;
  bit scenario_completed;

  function new(string name = "usb_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function time selected_test_timeout();
    return USB_TEST_TIMEOUT;
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Derived tests choose their budget through selected_test_timeout(); lock
    // it here so later set_timeout() calls cannot extend the scenario's bound.
    uvm_root::get().set_timeout(selected_test_timeout(), 0);
    env = usb_env::type_id::create("env", this);
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (!scenario_completed) begin
      `uvm_fatal("USB_INCOMPLETE", "Selected USB test did not complete its scenario")
    end
  endfunction

  function void report_phase(uvm_phase phase);
    uvm_report_server reports;

    super.report_phase(phase);
    reports = uvm_report_server::get_server();
    if (scenario_completed &&
        reports.get_severity_count(UVM_ERROR) == 0 &&
        reports.get_severity_count(UVM_FATAL) == 0) begin
      `uvm_info("USB_TEST_PASS", $sformatf("%s completed all required checks", get_type_name()), UVM_NONE)
      $display("* TESTCASE PASSED");
    end else begin
      `uvm_info("USB_TEST_FAIL", "USB scenario did not satisfy the pass criteria", UVM_NONE)
      $display("* TESTCASE FAILED");
    end
  endfunction
endclass
