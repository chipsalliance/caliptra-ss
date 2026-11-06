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
//
// Active test-local access adapter, deliberately separate from the passive
// observer. Reuse the subsystem's existing AXI BFM, never a second bus driver.
// Only the two RO diagnostic addresses are accessible to the register test.
`include "soc_address_map_defines.svh"
`include "soc_address_map_field_defines.svh"
interface caliptra_ss_usb_supersession_csr_if(input logic [31:0] axi_user);
    import axi_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    bit enabled = 0;

    function automatic logic [31:0] csr_address(input bit setup_debug);
        return setup_debug ? `SOC_USB_COMBO_RECOVERY_CALIPTRA_SETUP_DEBUG :
                             `SOC_USB_COMBO_RECOVERY_CALIPTRA_STATUS;
    endfunction

    function automatic void check_map();
        if ((`SOC_USB_COMBO_RECOVERY_CALIPTRA_SETUP_DEBUG !==
             (`SOC_USB_COMBO_BASE_ADDR + 32'hA08)) ||
            (`SOC_USB_COMBO_RECOVERY_CALIPTRA_STATUS !==
             (`SOC_USB_COMBO_BASE_ADDR + 32'hA04)) ||
            (`RECOVERY_CALIPTRA_SETUP_DEBUG_GENERATION_LOW != 0) ||
            (`RECOVERY_CALIPTRA_SETUP_DEBUG_GENERATION_MASK !== 32'hFFF) ||
            (`RECOVERY_CALIPTRA_SETUP_DEBUG_OWNER_OCP_LOW != 12) ||
            (`RECOVERY_CALIPTRA_SETUP_DEBUG_OWNER_OCP_MASK !== 32'h1000) ||
            (`RECOVERY_CALIPTRA_STATUS_POST_SYNC_ARB_STATE_LOW != 4) ||
            (`RECOVERY_CALIPTRA_STATUS_POST_SYNC_ARB_STATE_MASK !== 32'h70))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "Generated addresses/fields disagree with the diagnostic register contract")
    endfunction

    task automatic access(input bit setup_debug, input bit write_access,
                          input logic [31:0] write_data,
                          output logic [31:0] read_data,
                          output logic [1:0] response);
        axi_resp_e resp;
        if (!enabled || $isunknown(axi_user))
            `uvm_fatal("SUPERSESSION_DEBUG_CSR", "CSR adapter used while disabled or with unknown AXI USER")
        read_data = 'x;
        if (write_access)
            caliptra_ss_top_tb.u_caliptra_ss_top_tb_soc_bfm.bfm_axi_write_single_response(
                csr_address(setup_debug), axi_user, write_data, resp);
        else
            caliptra_ss_top_tb.u_caliptra_ss_top_tb_soc_bfm.bfm_axi_read_single_response(
                csr_address(setup_debug), axi_user, read_data, resp);
        response = resp;
    endtask
endinterface
