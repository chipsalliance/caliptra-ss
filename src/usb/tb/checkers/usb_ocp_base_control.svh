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

class usb_ocp_base_control extends uvm_object;
  `uvm_object_utils(usb_ocp_base_control)
  typedef struct {
    logic valid;
    logic [31:0] value;
    longint unsigned version;
    longint unsigned order;
    realtime observed_at;
  } status_version_t;
  status_version_t status_versions[$];
  logic status_read;
  logic status_frozen;
  longint unsigned status_setup_order;
  longint unsigned status_data_order;
  longint unsigned replaced_at;
  logic [7:0] setup[8];
  logic [7:0] data[$];
  logic [7:0] expected[$];
  logic active;
  logic status_acked;
  logic next_toggle[2] = '{1'b1, 1'b1};
  int unsigned generation;
  int unsigned epoch;
  logic [6:0] address;
  logic [7:0] configuration;
  int unsigned compared;

  function new(string name = "usb_ocp_base_control");
    super.new(name);
    active = 0;
    status_acked = 0;
    generation = 0;
    epoch = 0;
    address = 0;
    configuration = 0;
    compared = 0;
    status_read = 0;
    status_frozen = 0;
    status_setup_order = 0;
    status_data_order = 0;
    replaced_at = 0;
  endfunction

  function int unsigned ocp_get_length();
    return {setup[7], setup[6]};
  endfunction

  function logic [15:0] ocp_get_value();
    return {setup[3], setup[2]};
  endfunction

  function logic [15:0] ocp_get_index();
    return {setup[5], setup[4]};
  endfunction
endclass
