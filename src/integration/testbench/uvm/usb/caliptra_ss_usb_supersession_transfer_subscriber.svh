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

`ifndef CALIPTRA_SS_USB_SUPERSESSION_TRANSFER_SUBSCRIBER_SVH
`define CALIPTRA_SS_USB_SUPERSESSION_TRANSFER_SUBSCRIBER_SVH
// The environment republishes the active protocol's transfer-ended event,
// including intentional aborts. The checker copies only the request header.
class caliptra_ss_usb_supersession_transfer_subscriber
    extends uvm_subscriber#(svt_usb_transfer);
    `uvm_component_utils(caliptra_ss_usb_supersession_transfer_subscriber)
    caliptra_ss_usb_supersession_checker sink;

    function new(string name = "caliptra_ss_usb_supersession_transfer_subscriber",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void write(svt_usb_transfer t);
        if ((sink == null) || (t == null))
            `uvm_fatal("SUPERSESSION_PORT", "Null protocol analysis sink or transfer")
        sink.observe_transfer(t);
    endfunction
endclass
`endif
