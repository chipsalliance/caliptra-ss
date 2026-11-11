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

`ifndef CALIPTRA_SS_USB_SUPERSESSION_EVIDENCE_SVH
`define CALIPTRA_SS_USB_SUPERSESSION_EVIDENCE_SVH

// Value-only evidence for the single-packet control reads used by these tests.
// No vendor payload or packet handle survives an analysis write.
class caliptra_ss_usb_supersession_evidence extends uvm_sequence_item;
    `uvm_object_utils(caliptra_ss_usb_supersession_evidence)

    logic [15:0] generation;
    logic [63:0] setup_bytes;
    logic [15:0] recovery_interface;
    logic [7:0] data[$], pending_data[$];
    int setup_acks = 0, data_acks = 0, status_acks = 0, status_nyets = 0;
    int in_tokens = 0, out_tokens = 0, ping_tokens = 0, naks = 0, data_packets = 0;
    int ping_acks = 0, status_starts = 0, stalls = 0;
    bit setup_data, data_pending, status_data, checked, valid;
    bit released, notified, intentional_stale, fresh_service;
    logic [15:0] service_generation;
    realtime setup_at, setup_ack_at, data_ack_at, status_complete_at;
    realtime first_status_start_at;
    realtime nak_at, first_data_at, release_at;

    function new(string name = "caliptra_ss_usb_supersession_evidence");
        super.new(name);
    endfunction

    function int ocp_supersession_get_status_completions();
        return status_acks + status_nyets;
    endfunction

    // Classification uses observed request bytes, not a sequence's label.
    function bit ocp_supersession_check_is_ocp();
        return setup_data &&
               ((setup_bytes[7:0] === 8'hA1) || (setup_bytes[7:0] === 8'h21)) &&
               (setup_bytes[15:8] === OCP_BREQUEST_XFER) &&
               (setup_bytes[47:32] === recovery_interface);
    endfunction
endclass
`endif
