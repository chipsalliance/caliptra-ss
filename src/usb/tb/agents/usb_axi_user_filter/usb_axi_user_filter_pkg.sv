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
// UVM agent for one AXI USER filter policy (usb_axi_user_filter_if): an
// enable and an allowlist of privileged AXI USER values. Every class is
// parameterized by the USER width (UW) and allowlist depth (NUM_USERS) to
// match the interface it controls. Kept independent of usb_tb_pkg so the
// agent can be compiled before the bench package.
package usb_axi_user_filter_pkg;
  timeunit 1ns;
  timeprecision 1ps;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // SAMPLE drives nothing and returns the current policy. SET_ENABLE and
  // SET_USERS update one field group; SET_POLICY updates both on one edge.
  typedef enum {
    USB_AXI_USER_FILTER_SAMPLE,
    USB_AXI_USER_FILTER_SET_ENABLE,
    USB_AXI_USER_FILTER_SET_USERS,
    USB_AXI_USER_FILTER_SET_POLICY
  } usb_axi_user_filter_op_e;

  `include "usb_axi_user_filter_item.svh"
  `include "usb_axi_user_filter_agent_cfg.svh"
  `include "usb_axi_user_filter_sequencer.svh"
  `include "usb_axi_user_filter_driver.svh"
  `include "usb_axi_user_filter_monitor.svh"
  `include "usb_axi_user_filter_agent.svh"
  `include "usb_axi_user_filter_api_seq.svh"
endpackage
