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

`ifndef CALIPTRA_SS_USB_OCP_RAW_RESPONSE_CALLBACK_SVH
`define CALIPTRA_SS_USB_OCP_RAW_RESPONSE_CALLBACK_SVH

// Direct packet probes have no owning svt_usb_transfer. Link-monitor evidence
// remains visible, but the idle protocol engine must not process their replies
// as unsolicited normal-transfer traffic. Enable only inside raw windows.
class caliptra_ss_usb_ocp_raw_response_callback
    extends svt_usb_protocol_callbacks;
    `uvm_object_utils(caliptra_ss_usb_ocp_raw_response_callback)

    bit enabled;

    function new(string name = "caliptra_ss_usb_ocp_raw_response_callback");
        super.new(name);
    endfunction

    virtual function void post_usb_20_packet_in_port_get(
        svt_usb_protocol component, int chan_id,
        svt_usb_packet packet, ref bit drop);
        if (enabled && (packet != null)) drop = 1'b1;
    endfunction
endclass

`endif
