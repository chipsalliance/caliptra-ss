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

`ifndef CALIPTRA_SS_USB_STALE_PUBLICATION_PROTOCOL_SVH
`define CALIPTRA_SS_USB_STALE_PUBLICATION_PROTOCOL_SVH

// Hold only the selected control read's first IN transaction. SETUP and the
// separate SOF processor retain their normal VIP behavior.
class caliptra_ss_usb_stale_publication_protocol extends svt_usb_protocol;
    `uvm_component_utils(caliptra_ss_usb_stale_publication_protocol)

    protected bit armed, published, first_in_released;
    protected logic [15:0] generation;
    protected logic [63:0] expected_setup;
    protected logic [6:0] address;
    protected svt_usb_transfer actual_transfer;
    localparam time PUBLICATION_TIMEOUT = 20us;

    function new(string name = "caliptra_ss_usb_stale_publication_protocol",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void ocp_stale_configure_gate(
        input svt_usb_transfer request, input logic [15:0] gen);
        if (armed || (request == null) ||
            (request.xfer_type != svt_usb_transfer::CONTROL_TRANSFER) ||
            (request.endpoint_number != 0) ||
            (request.setup_data_bmrequesttype_dir != svt_usb_types::DEVICE_TO_HOST) ||
            (request.setup_data_w_length == 0))
            `uvm_fatal("STALE_PUBLICATION", "Invalid or overlapping publication gate")
        generation = gen;
        expected_setup =
            caliptra_ss_usb_supersession_checker::ocp_supersession_get_setup_line(request);
        address = request.device_address;
        actual_transfer = null;
        published = 0;
        first_in_released = 0;
        armed = 1;
    endfunction

    function void ocp_stale_configure_publication(input logic [15:0] gen);
        if (!armed || (generation !== gen) || (actual_transfer == null) ||
            published || first_in_released)
            `uvm_fatal("STALE_PUBLICATION", "Unbound or out-of-generation publication")
        published = 1;
    endfunction

    // The documented protocol task runs before a transaction's TOKEN is
    // created. The callback facade is a function and cannot hold this boundary.
    virtual task pre_transaction_cb_exec(svt_usb_transfer transfer,
                                         int transaction_ix);
        svt_usb_transaction transaction;
        logic [15:0] bound_generation;
        super.pre_transaction_cb_exec(transfer, transaction_ix);
        if (!armed || (transfer == null) ||
            (transfer.xfer_type != svt_usb_transfer::CONTROL_TRANSFER) ||
            (transfer.device_address != address) ||
            (transfer.endpoint_number != 0)) return;
        if (caliptra_ss_usb_supersession_checker::ocp_supersession_get_setup_line(transfer)
                !== expected_setup)
            `uvm_fatal("STALE_PUBLICATION", "Unexpected serialized control request")
        if ((transaction_ix < 0) || (transaction_ix >= transfer.implementation.size()) ||
            !$cast(transaction, transfer.implementation[transaction_ix]))
            `uvm_fatal("STALE_PUBLICATION", "Missing actual transaction")
        if (transaction.xact_type == svt_usb_types::SETUP_TRANSACTION) begin
            if (actual_transfer != null)
                `uvm_fatal("STALE_PUBLICATION", "Duplicate SETUP binding")
            // Sequence submissions may be copied; bind the actual VIP object.
            actual_transfer = transfer;
        end else if (transaction.xact_type == svt_usb_types::IN_TRANSACTION) begin
            if (actual_transfer != transfer)
                `uvm_fatal("STALE_PUBLICATION", "IN did not match the bound SETUP")
            if (first_in_released) return;
            bound_generation = generation;
            fork : bounded_publication
                wait (published || !armed || (generation !== bound_generation));
                #(PUBLICATION_TIMEOUT);
            join_any
            disable bounded_publication;
            if (!armed || !published || (generation !== bound_generation))
                `uvm_fatal("STALE_PUBLICATION", "Publication gate timed out or changed generation")
            first_in_released = 1;
        end
    endtask

    function void ocp_stale_check_and_retire_gate(input logic [15:0] gen);
        if (!armed || !published || !first_in_released ||
            (generation !== gen) || (actual_transfer == null) ||
            !actual_transfer.end_event.is_on() ||
            !caliptra_ss_usb_xfer_successful(actual_transfer))
            `uvm_fatal("STALE_PUBLICATION", "Gated transfer did not retire successfully")
        armed = 0;
        actual_transfer = null;
    endfunction
endclass
`endif
