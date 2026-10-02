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
// Issue one policy operation and wait for its response. Set op plus the
// fields it updates before start(). Afterwards observed_enable and
// observed_priv_axi_users hold the policy the DUT sees. A SET_* operation
// whose updated fields do not read back as requested is fatal.
class usb_axi_user_filter_api_seq #(
  int unsigned UW = 32,
  int unsigned NUM_USERS = 2
) extends uvm_sequence #(usb_axi_user_filter_item #(UW, NUM_USERS));
  `uvm_object_param_utils(usb_axi_user_filter_api_seq #(UW, NUM_USERS))

  typedef usb_axi_user_filter_item #(UW, NUM_USERS) item_t;

  rand usb_axi_user_filter_op_e op = USB_AXI_USER_FILTER_SAMPLE;
  rand bit enable;
  rand bit [UW-1:0] priv_axi_users [NUM_USERS];

  logic observed_enable;
  logic [UW-1:0] observed_priv_axi_users [NUM_USERS];

  function new(string name = "usb_axi_user_filter_api_seq");
    super.new(name);
  endfunction

  task body();
    item_t request;
    item_t response;

    request = item_t::type_id::create("request");
    start_item(request);
    request.op = op;
    request.enable = enable;
    request.priv_axi_users = priv_axi_users;
    finish_item(request);
    get_response(response);

    observed_enable = response.observed_enable;
    observed_priv_axi_users = response.observed_priv_axi_users;
    if (request.updates_enable() && observed_enable !== enable) begin
      `uvm_fatal("USB_USER_FILTER_API_SEQ", $sformatf("%s: enable read back %b, expected %0b", get_full_name(), observed_enable, enable))
    end
    if (request.updates_users()) begin
      foreach (priv_axi_users[index]) begin
        if (observed_priv_axi_users[index] !== priv_axi_users[index]) begin
          `uvm_fatal("USB_USER_FILTER_API_SEQ", $sformatf("%s: allowlist entry %0d read back 0x%0h, expected 0x%0h", get_full_name(), index, observed_priv_axi_users[index], priv_axi_users[index]))
        end
      end
    end
  endtask
endclass
