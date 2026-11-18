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
    protected bit termination_gate, hold_status, cancelled;
    protected bit address_status_gate;
    protected bit termination_transfer_ended;
    protected logic [15:0] termination_end_generation;
    protected svt_usb_transfer termination_ended_transfer;
    bit termination_boundary_reached;
    localparam time PUBLICATION_TIMEOUT = 20us;

    function new(string name = "caliptra_ss_usb_stale_publication_protocol",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void ocp_stale_configure_gate(
        input svt_usb_transfer request, input logic [15:0] gen,
        input bit zero_status = 0);
        if (armed || (request == null) ||
            (request.xfer_type != svt_usb_transfer::CONTROL_TRANSFER) ||
            (request.endpoint_number != 0) ||
            (!zero_status &&
             ((request.setup_data_bmrequesttype_dir != svt_usb_types::DEVICE_TO_HOST) ||
              (request.setup_data_w_length == 0))) ||
            (zero_status &&
             ((request.setup_data_bmrequesttype_dir != svt_usb_types::HOST_TO_DEVICE) ||
              (request.setup_data_bmrequesttype_type != svt_usb_types::STANDARD) ||
              (request.setup_data_bmrequesttype_recipient != svt_usb_types::BMREQ_DEVICE) ||
              (request.setup_data_brequest != 8'h05) ||
              (request.setup_data_w_index != 0) || (request.setup_data_w_length != 0) ||
              !(request.setup_data_w_value inside {[1:127]}))))
            `uvm_fatal("STALE_PUBLICATION", "Invalid or overlapping publication gate")
        generation = gen;
        expected_setup =
            caliptra_ss_usb_supersession_checker::ocp_supersession_get_setup_line(request);
        address = request.device_address;
        actual_transfer = null;
        termination_gate = 0;
        address_status_gate = zero_status;
        termination_boundary_reached = 0;
        termination_transfer_ended = 0;
        termination_end_generation = '0;
        termination_ended_transfer = null;
        cancelled = 0;
        published = 0;
        first_in_released = 0;
        armed = 1;
    endfunction

    // USB 2.0 9.4.6 has no DATA stage. Hold before the first STATUS IN
    // token, regardless of the VIP's IN/STATUS transaction classification.
    function void ocp_address_configure_gate(
        input svt_usb_transfer request, input logic [15:0] gen);
        if ((request == null) || (gen === 16'd0) || $isunknown(gen) ||
            (request.device_address === 7'd0) ||
            (request.setup_data_w_value === {9'd0, request.device_address})) begin
            `uvm_error("SETUP_ADDRESS_GATE", "Missing generation/nonzero distinct address gate binding")
            `uvm_fatal("SETUP_ADDRESS_GATE", "Cannot qualify Address-state SET_ADDRESS")
        end
        ocp_stale_configure_gate(request, gen, 1);
        termination_gate = 1;
        hold_status = 1;
    endfunction

    function void ocp_termination_configure_gate(
        input svt_usb_transfer request, input logic [15:0] gen,
        input bit status_pending);
        ocp_stale_configure_gate(request, gen);
        termination_gate = 1;
        hold_status = status_pending;
    endfunction

    function void ocp_termination_release_gate(input logic [15:0] gen,
                                              input bit teardown);
        if (!armed || !termination_gate || !termination_boundary_reached ||
            (generation !== gen) || (actual_transfer == null) || published) begin
            `uvm_error("SETUP_TERMINATION_GATE", "Unqualified termination gate release")
            `uvm_fatal("SETUP_TERMINATION_GATE", "Unqualified termination gate release")
        end
        // Abort only bookkeeping AFTER the observed teardown action. Never
        // cancel the VIP worker's process tree, which also owns SOF workers.
        cancelled = teardown;
        `uvm_info("SETUP_TERMINATION_NATIVE", $sformatf(
            "gen=%0d teardown=%b native-ended=%b protocol-ended=%b status=%s results=%032h",
            generation, teardown, actual_transfer.end_event.is_on(),
            termination_transfer_ended,
            actual_transfer.status.name(), actual_transfer.results_status), UVM_NONE)
        if (termination_transfer_ended &&
            (!teardown || caliptra_ss_usb_xfer_successful(actual_transfer)))
            `uvm_error("SETUP_TERMINATION_NATIVE",
                "VIP retired a still-gated transfer; cleanup must not mask this outcome")
        if (teardown && !termination_transfer_ended) actual_transfer.abort(1'b1);
        published = 1;
    endfunction

    // The processor's pre-transaction task may be terminated by abort(1).
    // Its release latch is not transfer-retirement evidence. Use the actual
    // descriptor's terminal hook; the caller retains its existing watchdog.
    task ocp_termination_check_and_retire_gate(input logic [15:0] gen);
        if (!armed || !termination_gate || !published ||
            (generation !== gen) || (actual_transfer == null)) begin
            `uvm_error("SETUP_TERMINATION_GATE", "Unbound/out-of-generation retirement")
            `uvm_fatal("SETUP_TERMINATION_GATE", "Cannot retire an unbound gate")
        end
        wait (termination_transfer_ended);
        if ((termination_end_generation !== gen) ||
            (termination_ended_transfer != actual_transfer) ||
            (!cancelled && !first_in_released) ||
            !actual_transfer.end_event.is_on()) begin
            `uvm_error("SETUP_TERMINATION_GATE", "Actual gated VIP transfer did not retire")
            `uvm_fatal("SETUP_TERMINATION_GATE", "Cannot reuse an unretired gate")
        end
        if ((!cancelled && !caliptra_ss_usb_xfer_successful(actual_transfer)) ||
            (cancelled && (actual_transfer.status !== svt_sequence_item::ABORTED)))
            `uvm_error("SETUP_TERMINATION_GATE", "Actual VIP outcome disagrees with service/teardown")
        if (address_status_gate) begin
            `uvm_info("SETUP_ADDRESS_ACTUAL", $sformatf(
                "gen=%0d actual-object=%0d terminal-gen=%0d status=%s raw-results=%032h cancelled=%b released=%b end-event=%b",
                generation, actual_transfer.get_inst_id(), termination_end_generation,
                actual_transfer.status.name(), actual_transfer.results_status, cancelled,
                first_in_released, actual_transfer.end_event.is_on()), UVM_NONE)
            if (cancelled && (actual_transfer.results_status !== 128'd0))
                `uvm_error("SETUP_ADDRESS_GATE", "Actual aborted SET_ADDRESS has suspect native result bits")
        end
        armed = 0;
        actual_transfer = null;
    endtask

    // Official svt_usb_protocol terminal local call, distinct from its
    // component-wide NOTIFY_USB_TRANSFER_ENDED event and from stage events.
    virtual function void transfer_ended(svt_usb_transfer transfer);
        super.transfer_ended(transfer);
        if (armed && termination_gate && (transfer != null) &&
            (transfer == actual_transfer)) begin
            if (termination_transfer_ended)
                `uvm_error("SETUP_TERMINATION_GATE", "Duplicate actual transfer-ended hook")
            termination_end_generation = generation;
            termination_ended_transfer = transfer;
            termination_transfer_ended = 1;
        end
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
                !== expected_setup) begin
            if (termination_gate)
                `uvm_error("SETUP_TERMINATION_GATE", "Unexpected serialized control request")
            `uvm_fatal("STALE_PUBLICATION", "Unexpected serialized control request")
        end
        if ((transaction_ix < 0) || (transaction_ix >= transfer.implementation.size()) ||
            !$cast(transaction, transfer.implementation[transaction_ix])) begin
            if (termination_gate)
                `uvm_error("SETUP_TERMINATION_GATE", "Missing actual VIP transaction")
            `uvm_fatal("STALE_PUBLICATION", "Missing actual transaction")
        end
        if (transaction.xact_type == svt_usb_types::SETUP_TRANSACTION) begin
            if (actual_transfer != null) begin
                if (termination_gate)
                    `uvm_error("SETUP_TERMINATION_GATE", "Duplicate SETUP binding")
                `uvm_fatal("STALE_PUBLICATION", "Duplicate SETUP binding")
            end
            // Sequence submissions may be copied; bind the actual VIP object.
            actual_transfer = transfer;
        end else if ((!termination_gate &&
                      (transaction.xact_type == svt_usb_types::IN_TRANSACTION)) ||
                     (termination_gate && !hold_status &&
                      (transaction.xact_type == svt_usb_types::IN_TRANSACTION)) ||
                     (address_status_gate &&
                      (transaction.xact_type inside {
                          svt_usb_types::IN_TRANSACTION, svt_usb_types::STATUS_TRANSACTION})) ||
                     (termination_gate && hold_status && !address_status_gate &&
                      (transaction.xact_type inside {
                          svt_usb_types::OUT_TRANSACTION,
                          svt_usb_types::STATUS_TRANSACTION,
                          svt_usb_types::PING_TRANSACTION}))) begin
            if (actual_transfer != transfer) begin
                if (termination_gate)
                    `uvm_error("SETUP_TERMINATION_GATE", "Stage did not match the bound SETUP")
                `uvm_fatal("STALE_PUBLICATION", "IN did not match the bound SETUP")
            end
            if (first_in_released) return;
            bound_generation = generation;
            if (termination_gate) termination_boundary_reached = 1;
            fork : bounded_publication
                wait (published || !armed || (generation !== bound_generation) ||
                      (termination_gate && termination_transfer_ended));
                begin
                    if (address_status_gate) #100us;
                    else if (termination_gate) #100ms;
                    else #(PUBLICATION_TIMEOUT);
                end
            join_any
            disable bounded_publication;
            // If the task survives a native abort, leave without sending the
            // held token or changing the next window's release bookkeeping.
            if (termination_gate && termination_transfer_ended &&
                (termination_end_generation === bound_generation) &&
                (generation === bound_generation) && (termination_ended_transfer == transfer))
                return;
            if (!armed || !published || (generation !== bound_generation)) begin
                if (termination_gate)
                    `uvm_error("SETUP_TERMINATION_GATE", "Pending-stage gate timed out")
                `uvm_fatal("STALE_PUBLICATION", "Publication gate timed out or changed generation")
            end
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
