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

class usb_vip_packet extends uvm_object;
  `uvm_object_utils(usb_vip_packet)

  byte unsigned bytes[$];
  realtime observed_at;
  realtime completed_at;
  realtime payload_completed_at;

  function new(string name = "usb_vip_packet");
    super.new(name);
  endfunction

  function bit is_data();
    return bytes.size() != 0 &&
           bytes[0] inside {8'hc3, 8'h4b, 8'h87, 8'h0f};
  endfunction
endclass
