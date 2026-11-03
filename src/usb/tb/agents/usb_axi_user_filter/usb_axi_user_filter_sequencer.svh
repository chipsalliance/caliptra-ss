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
//
// Sequencer for one AXI USER filter policy agent.
class usb_axi_user_filter_sequencer #(
  int unsigned UW = 32,
  int unsigned NUM_USERS = 2
) extends uvm_sequencer #(usb_axi_user_filter_item #(UW, NUM_USERS));
  `uvm_component_param_utils(usb_axi_user_filter_sequencer #(UW, NUM_USERS))

  function new(string name = "usb_axi_user_filter_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction
endclass
