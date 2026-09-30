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

// Helpers for the subsystem USB AXI USER filter tests. The filter policy itself
// (allowlists and enables) is driven by the USB AXI USER FILTERING POLICY section
// of caliptra_ss_top_tb_soc_bfm.sv; these helpers only read it.

// One location on each of the four independently wired USB AXI-to-AHB converters.
// The Combo converter carries DEV0 CSR, Hub, and Recovery traffic; it and the
// DEV0 SRAM converter use the Combo policy. The DEV1 CSR and DEV1 SRAM
// converters use the DEV1 policy.
typedef enum int {
    USB_AXI_FILTER_DEV0_CSR  = 0,
    USB_AXI_FILTER_DEV0_SRAM = 1,
    USB_AXI_FILTER_DEV1_CSR  = 2,
    USB_AXI_FILTER_DEV1_SRAM = 3
} usb_axi_filter_path_e;

localparam int USB_AXI_FILTER_NUM_PATHS         = 4;
localparam int USB_AXI_FILTER_NUM_INVALID_USERS = 2;

// The CSR target is INTROUTE, a plain read/write interrupt-routing register
// (EP routes [29:0], frame [30], device [31]) without W1C, FIFO, or action
// side effects. With the TB's USB_C_DEVx_NBPHYSEP_TB of 28 every bit is
// implemented, so the full word is compared.
localparam logic [31:0] USB_AXI_FILTER_INTROUTE_MASK = 32'hffff_ffff;

int unsigned usb_axi_filter_err_cnt;
int unsigned usb_axi_filter_check_cnt;

function automatic string usb_axi_filter_path_name(input usb_axi_filter_path_e path);
    case (path)
        USB_AXI_FILTER_DEV0_CSR:  return "DEV0 CSR (Combo INTROUTE)";
        USB_AXI_FILTER_DEV0_SRAM: return "DEV0 SRAM";
        USB_AXI_FILTER_DEV1_CSR:  return "DEV1 CSR (INTROUTE)";
        default:                  return "DEV1 SRAM";
    endcase
endfunction

function automatic logic [AXI_AW-1:0] usb_axi_filter_path_addr(input usb_axi_filter_path_e path);
    case (path)
        USB_AXI_FILTER_DEV0_CSR:  return `SOC_USB_COMBO_DEV0_CSR_INTROUTE;
        USB_AXI_FILTER_DEV0_SRAM: return `SOC_USB_DEV0_MEM_BASE_ADDR;
        USB_AXI_FILTER_DEV1_CSR:  return `SOC_USB_DEV1_CSR_INTROUTE;
        default:                  return `SOC_USB_DEV1_MEM_BASE_ADDR;
    endcase
endfunction

function automatic bit usb_axi_filter_path_is_csr(input usb_axi_filter_path_e path);
    return (path == USB_AXI_FILTER_DEV0_CSR) || (path == USB_AXI_FILTER_DEV1_CSR);
endfunction

function automatic bit usb_axi_filter_path_is_combo(input usb_axi_filter_path_e path);
    return (path == USB_AXI_FILTER_DEV0_CSR) || (path == USB_AXI_FILTER_DEV0_SRAM);
endfunction

function automatic logic [31:0] usb_axi_filter_path_mask(input usb_axi_filter_path_e path);
    return usb_axi_filter_path_is_csr(path) ? USB_AXI_FILTER_INTROUTE_MASK : 32'hffff_ffff;
endfunction

function automatic int unsigned usb_axi_filter_num_allowed_users(input usb_axi_filter_path_e path);
    return usb_axi_filter_path_is_combo(path) ? USB_COMBO_NUM_PRIV_AXI_USERS : USB_DEV1_NUM_PRIV_AXI_USERS;
endfunction

// Allowed USERs come from the finalized policy, so plusarg overrides are honored.
function automatic logic [31:0] usb_axi_filter_allowed_user(input usb_axi_filter_path_e path, input int unsigned slot);
    if (usb_axi_filter_path_is_combo(path))
        return cptra_ss_usb_combo_priv_axi_users_i[slot];
    return cptra_ss_usb_dev1_priv_axi_users_i[slot];
endfunction

function automatic bit usb_axi_filter_user_in_allowlists(input logic [31:0] user);
    foreach (cptra_ss_usb_combo_priv_axi_users_i[s])
        if (cptra_ss_usb_combo_priv_axi_users_i[s] === user)
            return 1'b1;
    foreach (cptra_ss_usb_dev1_priv_axi_users_i[s])
        if (cptra_ss_usb_dev1_priv_axi_users_i[s] === user)
            return 1'b1;
    return 1'b0;
endfunction

function automatic string usb_axi_filter_resp_str(input axi_resp_e resp);
    return $isunknown(resp) ? "X" : resp.name();
endfunction

// Picks distinct USERs that are absent from both finalized allowlists, including
// plusarg overrides. The generic invalid-USER helpers in common_axi_controls.svh
// exclude the MCU/MCI straps rather than the USB policy, so they are not used.
task automatic usb_axi_filter_get_invalid_users(output logic [31:0] users [USB_AXI_FILTER_NUM_INVALID_USERS]);
    logic [31:0] candidate;
    bit          reject;
    int unsigned tries;

    for (int i = 0; i < USB_AXI_FILTER_NUM_INVALID_USERS; i++) begin
        tries  = 0;
        reject = 1'b1;
        while (reject) begin
            tries++;
            if (tries > 1000)
                $fatal(1, "[%t] USB AXI FILTER: could not pick invalid USER %0d outside both allowlists", $time, i);
            candidate = $urandom();
            reject    = usb_axi_filter_user_in_allowlists(candidate);
            for (int j = 0; j < i; j++)
                if (users[j] === candidate)
                    reject = 1'b1;
        end
        users[i] = candidate;
        $display("[%t] USB AXI FILTER: invalid USER %0d = 0x%08h (in neither allowlist)", $time, i, candidate);
    end
endtask

// Single-beat write; checks only the AXI response.
task automatic usb_axi_filter_write(input usb_axi_filter_path_e path,
                                    input string               who,
                                    input logic [31:0]         user,
                                    input logic [31:0]         data,
                                    input axi_resp_e           exp_resp);
    logic [AXI_AW-1:0] addr;
    axi_resp_e         resp;

    addr = usb_axi_filter_path_addr(path);
    bfm_axi_write_single_response(addr, user, data, resp);
    usb_axi_filter_check_cnt++;
    if (resp !== exp_resp) begin
        usb_axi_filter_err_cnt++;
        $error("[%t] USB AXI FILTER: %s %s WRITE USER 0x%08h addr 0x%08h data 0x%08h: expected %s, got %s",
               $time, usb_axi_filter_path_name(path), who, user, addr, data,
               usb_axi_filter_resp_str(exp_resp), usb_axi_filter_resp_str(resp));
    end else begin
        $display("[%t] USB AXI FILTER: %s %s WRITE USER 0x%08h addr 0x%08h data 0x%08h: %s as expected",
                 $time, usb_axi_filter_path_name(path), who, user, addr, data, usb_axi_filter_resp_str(resp));
    end
endtask

// Single-beat read; checks the AXI response and the read data under mask. A mask
// of zero skips the data check (used to capture a CSR value before modifying it).
task automatic usb_axi_filter_read(input  usb_axi_filter_path_e path,
                                   input  string               who,
                                   input  logic [31:0]         user,
                                   input  logic [31:0]         exp_data,
                                   input  logic [31:0]         mask,
                                   input  axi_resp_e           exp_resp,
                                   output logic [31:0]         data);
    logic [AXI_AW-1:0] addr;
    axi_resp_e         resp;
    bit                ok;

    addr = usb_axi_filter_path_addr(path);
    bfm_axi_read_single_response(addr, user, data, resp);
    usb_axi_filter_check_cnt++;
    ok = (resp === exp_resp) && ((data & mask) === (exp_data & mask));
    if (!ok) begin
        usb_axi_filter_err_cnt++;
        $error("[%t] USB AXI FILTER: %s %s READ USER 0x%08h addr 0x%08h: expected %s data 0x%08h (mask 0x%08h), got %s data 0x%08h",
               $time, usb_axi_filter_path_name(path), who, user, addr,
               usb_axi_filter_resp_str(exp_resp), exp_data, mask, usb_axi_filter_resp_str(resp), data);
    end else begin
        $display("[%t] USB AXI FILTER: %s %s READ USER 0x%08h addr 0x%08h data 0x%08h: %s as expected",
                 $time, usb_axi_filter_path_name(path), who, user, addr, data, usb_axi_filter_resp_str(resp));
    end
endtask
