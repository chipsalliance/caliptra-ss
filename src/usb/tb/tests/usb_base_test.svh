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
// Provides common construction, configuration, timeout, completion, and final
// pass/fail reporting for standalone USB UVM tests. Derived tests must set
// scenario_completed only after all scenario-specific checking has finished.
//
// The test owns the environment configuration: build_phase creates usb_env_cfg
// with the bench defaults, lets the derived test adjust it through
// configure_env_cfg(), and publishes it to usb_env through uvm_config_db.
//
// Whole-test timeout, highest precedence first:
//   1. +UVM_TIMEOUT=<ns>[,YES|NO] on the command line (standard UVM plusarg,
//      applied by uvm_root before this build_phase runs).
//   2. uvm_config_db#(time) "test_timeout" set for this test by a parent.
//   3. test_timeout as assigned by the derived test's constructor.
class usb_base_test extends uvm_test;
  `uvm_component_utils(usb_base_test)

  usb_env env;
  usb_env_cfg env_cfg;
  bit scenario_completed;

  // Whole-test budget. A derived test that needs longer assigns this in its
  // constructor; apply_test_timeout() resolves overrides and applies it.
  time test_timeout = USB_DEFAULT_TEST_TIMEOUT;

  function new(string name = "usb_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Hook for a derived test to change the default configuration, for example
  // to advertise a different endpoint layout, before the environment uses it.
  virtual function void configure_env_cfg(usb_env_cfg cfg);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    apply_test_timeout();

    env_cfg = usb_env_cfg::type_id::create("env_cfg");
    env_cfg.build_endpoint_cfgs();
    configure_env_cfg(env_cfg);
    uvm_config_db#(usb_env_cfg)::set(this, "env", "cfg", env_cfg);
    `uvm_info("USB_TEST", $sformatf("%s configured: timeout=%0t %s", get_type_name(), test_timeout, env_cfg.convert2string()), UVM_LOW)
    `uvm_info("USB_TEST", {"Environment configuration:\n", env_cfg.sprint()}, UVM_HIGH)

    env = usb_env::type_id::create("env", this);
  endfunction

  // Resolve the whole-test timeout (see the class header for precedence) and
  // leave test_timeout holding the value actually in force. Without
  // +UVM_TIMEOUT the value is locked so components cannot extend it.
  function void apply_test_timeout();
    uvm_cmdline_processor clp = uvm_cmdline_processor::get_inst();
    string timeout_args[$];
    string source = "test default";

    if (uvm_config_db#(time)::get(this, "", "test_timeout", test_timeout)) begin
      source = "uvm_config_db";
    end
    if (clp.get_arg_values("+UVM_TIMEOUT=", timeout_args) > 0) begin
      `uvm_info("USB_TEST", $sformatf("+UVM_TIMEOUT=%s supersedes the %s timeout of %0t", timeout_args[0], source, test_timeout), UVM_LOW)
      source = "+UVM_TIMEOUT";
    end else begin
      uvm_root::get().set_timeout(test_timeout, 0);
    end
    test_timeout = uvm_root::get().phase_timeout;
    `uvm_info("USB_TEST", $sformatf("Whole-test timeout %0t from %s", test_timeout, source), UVM_LOW)
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
