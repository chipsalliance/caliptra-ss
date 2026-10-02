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
// One AXI USER filter policy operation. Requests carry op, enable, and
// priv_axi_users; the driver's response and every monitor item also carry
// the four-state policy observed on the interface after the operation.
class usb_axi_user_filter_item #(
  int unsigned UW = 32,
  int unsigned NUM_USERS = 2
) extends uvm_sequence_item;
  `uvm_object_param_utils(usb_axi_user_filter_item #(UW, NUM_USERS))

  typedef usb_axi_user_filter_item #(UW, NUM_USERS) this_t;

  rand usb_axi_user_filter_op_e op;
  rand bit enable;
  rand bit [UW-1:0] priv_axi_users [NUM_USERS];

  // Policy sampled by the clocking block one edge after the operation.
  logic observed_enable;
  logic [UW-1:0] observed_priv_axi_users [NUM_USERS];

  function new(string name = "usb_axi_user_filter_item");
    super.new(name);
  endfunction

  function bit updates_enable();
    return op inside {USB_AXI_USER_FILTER_SET_ENABLE, USB_AXI_USER_FILTER_SET_POLICY};
  endfunction

  function bit updates_users();
    return op inside {USB_AXI_USER_FILTER_SET_USERS, USB_AXI_USER_FILTER_SET_POLICY};
  endfunction

  virtual function void do_copy(uvm_object rhs);
    this_t rhs_item;

    super.do_copy(rhs);
    if (!$cast(rhs_item, rhs)) begin
      `uvm_fatal("USB_USER_FILTER_ITEM", "do_copy argument is not a usb_axi_user_filter_item of the same specialization")
    end
    op = rhs_item.op;
    enable = rhs_item.enable;
    priv_axi_users = rhs_item.priv_axi_users;
    observed_enable = rhs_item.observed_enable;
    observed_priv_axi_users = rhs_item.observed_priv_axi_users;
  endfunction

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    this_t rhs_item;

    if (!$cast(rhs_item, rhs) || !super.do_compare(rhs, comparer)) begin
      return 1'b0;
    end
    if (op != rhs_item.op || enable != rhs_item.enable || observed_enable !== rhs_item.observed_enable) begin
      return 1'b0;
    end
    for (int unsigned index = 0; index < NUM_USERS; index++) begin
      if (priv_axi_users[index] != rhs_item.priv_axi_users[index] || observed_priv_axi_users[index] !== rhs_item.observed_priv_axi_users[index]) begin
        return 1'b0;
      end
    end
    return 1'b1;
  endfunction

  virtual function string convert2string();
    string text;

    text = $sformatf("op=%s", op.name());
    if (updates_enable()) begin
      text = {text, $sformatf(" enable=%0b", enable)};
    end
    if (updates_users()) begin
      text = {text, " users="};
      foreach (priv_axi_users[index]) begin
        text = {text, $sformatf(" 0x%0h", priv_axi_users[index])};
      end
    end
    text = {text, $sformatf(" observed_enable=%b observed_users=", observed_enable)};
    foreach (observed_priv_axi_users[index]) begin
      text = {text, $sformatf(" 0x%0h", observed_priv_axi_users[index])};
    end
    return text;
  endfunction
endclass
