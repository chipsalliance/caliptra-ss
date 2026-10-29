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

//------------------------------------------------------------------------------
// Helper for the MCI_BOOT_FSM_GLITCH SV test (mci_boot_fsm_glitch.svh).
//
// The RTL and TB libraries each compile their own copy of mci_pkg, so a TB
// value of type mci_pkg::mci_boot_fsm_state_e cannot be assigned to the RTL
// boot FSM state signals. This module is bound into mci_boot_seqr, and the
// bind resolves mci_boot_fsm_state_e from mci_boot_seqr's own scope
// (IEEE 1800-2023 23.11). force_val therefore has the RTL enum type, and the
// test uses it as the right-hand side of its injection force.
//
// The module has no ports and does not drive any design signal by itself.
//------------------------------------------------------------------------------
module mci_boot_fsm_glitch_inject #(
    parameter type state_t = logic
) ();
    state_t force_val;

    function automatic void set_code(input logic [$bits(state_t)-1:0] code);
        force_val = state_t'(code);
    endfunction
endmodule

bind mci_boot_seqr mci_boot_fsm_glitch_inject #(.state_t(mci_boot_fsm_state_e)) u_mci_boot_fsm_glitch_inject ();
