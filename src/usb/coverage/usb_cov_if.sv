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

// Implementation coverage stays local: no samples or readiness events are
// exported to the USB stimulus or response scoreboard.
`ifndef VERILATOR
interface usb_cov_if (
    input logic hclk,
    input logic hresetn,
    input logic sync_busreset,
    input logic dev0_local_reset_c,
    input logic new_setup_c,
    input logic setup_owner_ocp_o,
    input logic [2:0] post_sync_arb_state_o,
    input logic usbreg_setup,
    input logic ocp_claim_abort_i,
    input logic fw_protocol_error_req_i,
    input logic ep0_ocp_owner_r,
    input logic setup_complete_c,
    input logic setup_valid_c,
    input logic setup_claim_c,
    input logic dma_set_int,
    input logic dma_txn_done_c,
    input logic dma_req_forward_c,
    input logic setup_dma_match_c,
    input logic sync_sieint_endtransfer_o,
    input logic sync_sieint_success_o
);

    localparam logic [2:0] IDLE = 0, MIRROR = 1, META_WAIT = 2,
                           DATA = 3, STATUS = 4, PROT_STALL = 5;
    bit setup_in_progress, state_history_valid;
    bit completion_pending;
    logic previous_owner, previous_pending;
    logic [2:0] previous_state, last_state;
    logic completion_owner, completion_success, notification_seen;

    covergroup setup_cg with function sample(
        logic valid_setup, logic new_owner, logic old_owner,
        logic [2:0] interrupted_state, logic old_setup_pending);
        option.per_instance = 1;
        valid_cp: coverpoint valid_setup {
            bins malformed = {0};
            bins accepted = {1};
        }
        new_owner_cp: coverpoint new_owner iff (valid_setup) {
            bins legacy = {0};
            bins ocp = {1};
        }
        old_owner_cp: coverpoint old_owner {
            bins legacy = {0};
            bins ocp = {1};
        }
        interrupted_state_cp: coverpoint interrupted_state {
            bins idle = {IDLE};
            bins mirror = {MIRROR};
            bins meta_wait = {META_WAIT};
            bins data_pending = {DATA};
            bins status_pending = {STATUS};
            bins protocol_stall = {PROT_STALL};
        }
        old_pending_cp: coverpoint old_setup_pending {
            bins released = {0};
            bins held = {1};
        }
        replacement_cross: cross old_owner_cp, new_owner_cp,
                                 interrupted_state_cp;
        held_replacement_cross: cross new_owner_cp, old_pending_cp;
    endgroup

    covergroup state_cg with function sample(
        logic [2:0] state, logic [2:0] prior_state, bit history_valid);
        option.per_instance = 1;
        state_cp: coverpoint state {
            bins idle = {IDLE};
            bins mirror = {MIRROR};
            bins meta_wait = {META_WAIT};
            bins data = {DATA};
            bins status = {STATUS};
            bins protocol_stall = {PROT_STALL};
        }
        replacement_cp: coverpoint {prior_state, state} iff (history_valid) {
            bins replace_data = {{DATA, MIRROR}};
            bins replace_status = {{STATUS, MIRROR}};
        }
    endgroup

    covergroup completion_cg with function sample(
        logic claimed, logic success, logic interrupt_posted);
        option.per_instance = 1;
        owner_cp: coverpoint claimed {
            bins legacy = {0};
            bins ocp = {1};
        }
        success_cp: coverpoint success {
            bins suppressed = {0};
            bins successful = {1};
        }
        notification_cp: coverpoint interrupt_posted {
            bins absent = {0};
            bins posted = {1};
        }
        completion_cross: cross owner_cp, success_cp, notification_cp;
    endgroup

    setup_cg setups = new();
    state_cg states = new();
    completion_cg completions = new();

    always @(posedge hclk) begin
        if ((hresetn !== 1'b1) ||
            (sync_busreset !== 1'b0) ||
            (dev0_local_reset_c !== 1'b0)) begin
            setup_in_progress = 0;
            state_history_valid = 0;
            completion_pending = 0;
        end else begin
            states.sample(post_sync_arb_state_o,
                          last_state, state_history_valid);
            last_state = post_sync_arb_state_o;
            state_history_valid = 1;
            if (new_setup_c === 1'b1) begin
                previous_owner = setup_owner_ocp_o;
                previous_state = post_sync_arb_state_o;
                previous_pending = usbreg_setup;
                setup_in_progress = 1;
            end else if ((ocp_claim_abort_i === 1'b1) ||
                         ((fw_protocol_error_req_i === 1'b1) &&
                          (ep0_ocp_owner_r === 1'b1))) begin
                setup_in_progress = 0;
            end else if (setup_in_progress &&
                         (post_sync_arb_state_o === MIRROR) &&
                         (setup_complete_c === 1'b1)) begin
                setups.sample(setup_valid_c,
                              setup_claim_c,
                              previous_owner, previous_state, previous_pending);
                setup_in_progress = 0;
            end

            // DMA can post notification after endtransfer. Observe the whole
            // matched response-valid lifecycle, not just its endtransfer edge.
            if (completion_pending) begin
                notification_seen |= dma_set_int;
                if (dma_txn_done_c === 1'b1) begin
                    completions.sample(completion_owner, completion_success,
                                       notification_seen);
                    completion_pending = 0;
                end else if ((new_setup_c === 1'b1) ||
                             (ocp_claim_abort_i === 1'b1) ||
                             (dma_req_forward_c === 1'b1)) begin
                    completion_pending = 0;
                end
            end
            if ((setup_dma_match_c === 1'b1) &&
                (sync_sieint_endtransfer_o === 1'b1) &&
                (new_setup_c === 1'b0) &&
                (ocp_claim_abort_i === 1'b0) &&
                (dma_req_forward_c === 1'b0)) begin
                completion_owner = setup_claim_c;
                completion_success = sync_sieint_success_o;
                notification_seen = dma_set_int;
                completion_pending = 1;
            end
        end
    end

    final begin
        $display("USB_IMPLEMENTATION_COVERAGE setup=%0.2f state=%0.2f completion=%0.2f (coverage only, not a correctness verdict)",
                 setups.get_inst_coverage(), states.get_inst_coverage(),
                 completions.get_inst_coverage());
    end

endinterface
`endif
