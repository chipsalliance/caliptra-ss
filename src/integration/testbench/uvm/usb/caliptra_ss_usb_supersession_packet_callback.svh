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

`ifndef CALIPTRA_SS_USB_SUPERSESSION_PACKET_CALLBACK_SVH
`define CALIPTRA_SS_USB_SUPERSESSION_PACKET_CALLBACK_SVH
typedef class caliptra_ss_usb_supersession_checker;

// Observe completed packets through the active host's documented callbacks.
// Copy values synchronously because the VIP may reuse packet/payload handles.
class caliptra_ss_usb_supersession_packet_callback extends svt_usb_link_monitor_callback;
    `uvm_object_utils(caliptra_ss_usb_supersession_packet_callback)
    caliptra_ss_usb_supersession_checker sink;

    function new(string name = "caliptra_ss_usb_supersession_packet_callback");
        super.new(name);
    endfunction

    virtual function void usb_20_rx_packet_ended(
        svt_usb_link_monitor link_mon, svt_usb_packet pkt);
        if ((sink == null) || (pkt == null))
            `uvm_fatal("SUPERSESSION_PORT", "Null analysis sink or object")
        sink.observe_packet(0, pkt);
    endfunction

    virtual function void usb_20_tx_packet_ended(
        svt_usb_link_monitor link_mon, svt_usb_packet pkt);
        if ((sink == null) || (pkt == null))
            `uvm_fatal("SUPERSESSION_PORT", "Null analysis sink or object")
        sink.observe_packet(1, pkt);
    endfunction
endclass
`endif
