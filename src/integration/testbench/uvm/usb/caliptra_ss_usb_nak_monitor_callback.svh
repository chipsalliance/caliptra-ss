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

`ifndef CALIPTRA_SS_USB_NAK_MONITOR_CALLBACK_SV
`define CALIPTRA_SS_USB_NAK_MONITOR_CALLBACK_SV

class caliptra_ss_usb_nak_monitor_callback
    extends svt_usb_link_monitor_callback;

    `uvm_object_utils(caliptra_ss_usb_nak_monitor_callback)

    protected static int unsigned nak_count;

    function new(string name = "caliptra_ss_usb_nak_monitor_callback");
        super.new(name);
    endfunction

    static function int unsigned get_nak_count();
        return nak_count;
    endfunction

    static function void reset_nak_count();
        nak_count = 0;
    endfunction

    virtual function void usb_20_rx_packet_ended(
        svt_usb_link_monitor link_mon,
        svt_usb_packet pkt);

        if ((pkt != null) &&
            (pkt.pid_type == svt_usb_packet::HANDSHAKE) &&
            (pkt.pid_name == svt_usb_packet::NAK)) begin
            nak_count++;
        end
    endfunction

endclass

class caliptra_ss_usb_ping_retry_callback
    extends svt_usb_protocol_callbacks;

    `uvm_object_utils(caliptra_ss_usb_ping_retry_callback)

    function new(string name = "caliptra_ss_usb_ping_retry_callback");
        super.new(name);
    endfunction

    virtual function void randomized_transaction(
        svt_usb_protocol component,
        svt_usb_transfer transfer,
        int transaction_ix,
        svt_usb_types::protocol_randomization_point_enum rand_point);

        svt_usb_transaction transaction;

        if ((transfer != null) &&
            (transfer.get_xfer_type_val() ==
                svt_usb_transfer::CONTROL_TRANSFER) &&
            $cast(transaction, transfer.implementation[transaction_ix])) begin
            // Synopsys USB VIP uses PING flow control for HS CONTROL OUT.
            // Pace retries so the Device-side EXT consumer can service the
            // available FIFO batch without creating a new SETUP.
            transaction.ping_to_ping_delay = 125us;
        end
    endfunction

endclass

`endif // CALIPTRA_SS_USB_NAK_MONITOR_CALLBACK_SV
