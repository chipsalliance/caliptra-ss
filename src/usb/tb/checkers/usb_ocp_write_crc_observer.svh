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

// A corrupted OUT DATA receives no handshake (USB 2.0 8.7.2), so the host
// records a device timeout before its retry. Permit that result bit only on
// the one transfer that actually carried the injected CRC16 error.
class usb_ocp_write_crc_observer extends usb_ocp_observer;
  `uvm_component_utils(usb_ocp_write_crc_observer)
  usb_ocp_write_crc_callback injection;

  function new(string name = "usb_ocp_write_crc_observer", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void ocp_configure_transfer_snapshot(
      svt_usb_transfer xfer, usb_ocp_event item);
    if (injection != null && injection.injected && xfer == injection.target)
      item.expected_device_timeout = 1;
  endfunction
endclass
