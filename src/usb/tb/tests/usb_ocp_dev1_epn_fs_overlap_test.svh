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

class usb_ocp_dev1_epn_fs_overlap_test extends usb_ocp_base_test;
  `uvm_component_utils(usb_ocp_dev1_epn_fs_overlap_test)

  function new(string name = "usb_ocp_dev1_epn_fs_overlap_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void configure_env_cfg(usb_env_cfg cfg);
    usb_ocp_base_env_cfg ocp_cfg;
    super.configure_env_cfg(cfg);
    if (!$cast(ocp_cfg,cfg))
      `uvm_fatal("OCP_FS_CONFIG", "FS testcase requires OCP configuration")
    ocp_cfg.full_speed = 1;
  endfunction

  task run_phase(uvm_phase phase);
    usb_ocp_dev1_epn_fs_overlap_seq scenario;
    phase.raise_objection(this);
    env.wait_for_reset();
    scenario = usb_ocp_dev1_epn_fs_overlap_seq::type_id::create("scenario");
    scenario.start(env.virtual_sequencer);
    scenario_completed = scenario.completed;
    phase.drop_objection(this);
  endtask
endclass
