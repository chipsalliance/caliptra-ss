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

class usb_ocp_dev0_ep0_interleave_seq extends usb_ocp_bringup_seq;
  `uvm_object_utils(usb_ocp_dev0_ep0_interleave_seq)
  usb_ocp_scoreboard scoreboard;

  function new(string name = "usb_ocp_dev0_ep0_interleave_seq");
    super.new(name);
  endfunction

  virtual function usb_ocp_base_host_seq ocp_prepare_host();
    usb_ocp_dev0_ep0_host_seq host;
    host = usb_ocp_dev0_ep0_host_seq::type_id::create("host");
    host.scoreboard = scoreboard;
    return host;
  endfunction

  task body();
    if (!uvm_config_db#(usb_ocp_scoreboard)::get(p_sequencer,"","ocp_scoreboard",scoreboard))
      `uvm_fatal("OCP_SUPERSESSION", "Missing mandatory replacement checker")
    scoreboard.model.require_dev0_ep0_replacement = 1;
    super.body();
  endtask
endclass
