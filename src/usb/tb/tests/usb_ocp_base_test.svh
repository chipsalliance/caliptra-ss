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

class usb_ocp_base_test extends usb_base_test;
  `uvm_component_utils(usb_ocp_base_test)

  function new(string name = "usb_ocp_base_test", uvm_component parent = null);
    super.new(name,parent);
    test_timeout = 3s;
  endfunction

  function void build_phase(uvm_phase phase);
    uvm_cmdline_processor cli;
    string args[$];
    int l2_faults = 0;
    int hub_faults = 0;
    int setup_retries = 0;
    cli = uvm_cmdline_processor::get_inst();
    cli.get_args(args);
    foreach (args[i]) begin
      if (uvm_is_match("+usb_ocp_peer_setup_retry*",args[i])) begin
        setup_retries++;
        if (get_type_name() != "usb_ocp_dev1_ep0_overlap_test" || setup_retries != 1 ||
            !(args[i] inside {"+usb_ocp_peer_setup_retry",
                              "+usb_ocp_peer_setup_retry=immediate"}))
          `uvm_fatal("OCP_SETUP_RETRY_GUARD", "Select one peer SETUP retry on the dev1 EP0 test")
      end
      if (uvm_is_match("+usb_ocp_l2_fault*",args[i])) begin
        l2_faults++;
        if (get_type_name() != "usb_ocp_suspend_resume_test" || l2_faults != 1 ||
            !(args[i] inside {"+usb_ocp_l2_fault=dsus","+usb_ocp_l2_fault=response"}))
          `uvm_fatal("OCP_L2_NEGATIVE", "Select one owned DSUS/response comparison control")
      end
      if (uvm_is_match("+usb_ocp_fs_hub_fault*",args[i])) begin
        hub_faults++;
        if (get_type_name() != "usb_ocp_dev1_epn_fs_overlap_test" || hub_faults != 1 ||
            args[i] != "+usb_ocp_fs_hub_fault=missing_interface")
          `uvm_fatal("OCP_FS_GUARD", "Missing-interface comparison control requires the FS EPN test")
      end
    end
    // Reject private FIFO selectors on other OCP tests before any actors.
    void'(usb_ocp_fifo_backpressure_epn_checker::ocp_check_control_args(
      get_type_name() == "usb_ocp_fifo_backpressure_epn_test"));
    if (get_type_name() != "usb_ocp_fifo_backpressure_epn_test")
      void'(usb_ocp_fifo_backpressure_ep0_checker::ocp_check_control_args(
        get_type_name() == "usb_ocp_fifo_backpressure_ep0_test"));
    // These instance overrides exist only when this OCP base test is selected.
    usb_env::type_id::set_inst_override(usb_ocp_base_env::get_type(),{get_full_name(),".env"});
    usb_env_cfg::type_id::set_inst_override(usb_ocp_base_env_cfg::get_type(),"env_cfg");
    usb_vip_cfg_builder::type_id::set_inst_override(usb_ocp_base_vip_cfg_builder::get_type(),"vip_cfg_builder");
    super.build_phase(phase);
  endfunction
endclass
