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
// Description:
//      Controller for the dedicated MCU ROM patch SRAM. MCU ROM copies a patch
//      (typically from the vendor non-secret fuse partition) into this SRAM and
//      fetches patch instructions from it.
//
//      Security rules (all enforced in HW):
//      Write : MCU LSU only, full-word only, and only while
//                - LC state is TEST_LOCKED0-6, TEST_UNLOCKED0-7 or DEV (valid, no fatal LC error)
//                - Caliptra core has not left reset yet in this power cycle, both
//                  at the MCI boot sequencer and at the Caliptra core reset input
//      Read  : MCU LSU/IFU only, and only while the patch flag is set and the
//              LC condition above still holds. The LC re-check blocks a
//              stale patch from running after a DEV->PROD transition plus a
//              warm reset (the flag and SRAM contents survive a warm reset).
//      Flag  : mcu_rom_patch_active_o is set by the first accepted write and is
//              cleared only by a cold reset (mci_pwrgood). It is stable before
//              Caliptra core leaves reset. It blocks UDS/FE provisioning in the
//              fuse controller filter and zeroizes the UDS/FE delivered to
//              Caliptra core.
//
//      Any other access returns an error on the first cycle of cif_resp_if.
//      ECC errors are returned on the read data phase (second cycle).
`include "caliptra_sva.svh"


module mci_mcu_rom_patch_ctrl
    #(
    parameter  MCU_ROM_PATCH_SRAM_SIZE_KB = 4
    ,localparam BITS_IN_BYTE = 8
    ,localparam KB = 1024 // Bytes in KB

    ,localparam MCU_ROM_PATCH_SRAM_SIZE_BYTES = MCU_ROM_PATCH_SRAM_SIZE_KB * KB
    ,localparam MCU_ROM_PATCH_SRAM_DATA_W = 32 // ECC not parametrized
    ,localparam MCU_ROM_PATCH_SRAM_DATA_W_BYTES = MCU_ROM_PATCH_SRAM_DATA_W / BITS_IN_BYTE
    ,localparam MCU_ROM_PATCH_SRAM_ECC_DATA_W = 7 // ECC not parametrized
    ,localparam MCU_ROM_PATCH_SRAM_DEPTH = MCU_ROM_PATCH_SRAM_SIZE_BYTES / MCU_ROM_PATCH_SRAM_DATA_W_BYTES
    ,localparam MCU_ROM_PATCH_SRAM_ADDR_W = $clog2(MCU_ROM_PATCH_SRAM_DEPTH)

    // Number of address bits needed on cif_resp_if.addr to address the entire SRAM
    ,localparam MCU_ROM_PATCH_SRAM_CIF_ADDR_W = $clog2(MCU_ROM_PATCH_SRAM_SIZE_BYTES)
    )
    (
    input logic clk,

    // Warm reset (datapath) and cold reset (sticky patch flag)
    input logic rst_b,
    input logic mci_pwrgood,

    // Caliptra core reset from the MCI boot sequencer, and as seen at the
    // Caliptra core reset input (the SoC may not loop the MCI output back)
    input logic cptra_rst_b,
    input logic cptra_core_rst_b_i,

    // LC state (static, sampled from OTP at boot)
    input lc_ctrl_state_pkg::lc_state_e otp_static_state_i,
    input logic                         otp_state_valid_i,
    input logic                         lc_fatal_state_error_i,

    // Privileged requests
    input logic axi_mcu_lsu_req,
    input logic axi_mcu_ifu_req,

    // Patch SRAM populated this power cycle (to fuse controller filter)
    output logic mcu_rom_patch_active_o,

    output logic sram_single_ecc_error,
    output logic sram_double_ecc_error,

    // Interface with SoC
    cif_if.response cif_resp_if,

    // Interface with SRAM
    mci_mcu_sram_if.request mci_mcu_rom_patch_sram_req_if
    );

//////////////////////////////////////
// Signal declarations
//////////////////////////////////////

logic otp_state_valid_q;
logic cptra_released_q;
logic lc_patch_allowed;
logic patch_wr_open;
logic patch_rd_open;

logic wr_filter_success;
logic rd_filter_success;
logic filter_error;

logic sram_req_second_cycle;
logic sram_read_req;
logic sram_write_req;
logic sram_read_data_avail;

logic [MCU_ROM_PATCH_SRAM_DATA_W-1:0]     sram_rdata;
logic [MCU_ROM_PATCH_SRAM_DATA_W-1:0]     sram_rdata_cor;
logic [MCU_ROM_PATCH_SRAM_ECC_DATA_W-1:0] sram_rdata_ecc;

///////////////////////////////////////////////
// Access policy
///////////////////////////////////////////////

// otp_state_valid_i is combinational from the fuse controller, but
// otp_static_state_i is registered in mci_lcc_st_trans on the same valid.
// Flop the valid so both describe the same cycle.
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        otp_state_valid_q <= 1'b0;
    end
    else begin
        otp_state_valid_q <= otp_state_valid_i;
    end
end

// Positive decode: patching is only permitted in TEST_LOCKED, TEST_UNLOCKED and MANUF (DEV).
// RAW, PROD, PROD_END, RMA, SCRAP and invalid encodings are closed.
always_comb begin
    lc_patch_allowed = 1'b0;
    if (otp_state_valid_q && !lc_fatal_state_error_i) begin
        case (otp_static_state_i)
            lc_ctrl_state_pkg::LcStTestLocked0,
            lc_ctrl_state_pkg::LcStTestLocked1,
            lc_ctrl_state_pkg::LcStTestLocked2,
            lc_ctrl_state_pkg::LcStTestLocked3,
            lc_ctrl_state_pkg::LcStTestLocked4,
            lc_ctrl_state_pkg::LcStTestLocked5,
            lc_ctrl_state_pkg::LcStTestLocked6,
            lc_ctrl_state_pkg::LcStTestUnlocked0,
            lc_ctrl_state_pkg::LcStTestUnlocked1,
            lc_ctrl_state_pkg::LcStTestUnlocked2,
            lc_ctrl_state_pkg::LcStTestUnlocked3,
            lc_ctrl_state_pkg::LcStTestUnlocked4,
            lc_ctrl_state_pkg::LcStTestUnlocked5,
            lc_ctrl_state_pkg::LcStTestUnlocked6,
            lc_ctrl_state_pkg::LcStTestUnlocked7,
            lc_ctrl_state_pkg::LcStDev: lc_patch_allowed = 1'b1;
            default:                    lc_patch_allowed = 1'b0;
        endcase
    end
end

// Caliptra core captures UDS/FE only on its first reset release of a power cycle
// (CPTRA_FUSE_WR_DONE is cleared by pwrgood only). Writes are only allowed before
// that release, so a patch can never be loaded after Caliptra core captured the
// real UDS/FE (e.g. after a warm reset).
always_ff @(posedge clk or negedge mci_pwrgood) begin
    if (!mci_pwrgood) begin
        cptra_released_q <= 1'b0;
    end
    else if (cptra_rst_b || cptra_core_rst_b_i) begin
        cptra_released_q <= 1'b1;
    end
end

// Writes close permanently (until the next cold reset) once Caliptra core is
// released, so the patch flag is stable before Caliptra core samples UDS/FE.
assign patch_wr_open = lc_patch_allowed & ~cptra_rst_b & ~cptra_core_rst_b_i & ~cptra_released_q;

// Reads (IFU fetch / LSU readback) only when this power cycle's patch is present.
assign patch_rd_open = lc_patch_allowed & mcu_rom_patch_active_o;

// Full-word writes only: no RMW path is needed to load a patch.
assign wr_filter_success = cif_resp_if.dv &  cif_resp_if.req_data.write & axi_mcu_lsu_req &
                           (&cif_resp_if.req_data.wstrb) & patch_wr_open;
assign rd_filter_success = cif_resp_if.dv & ~cif_resp_if.req_data.write &
                           (axi_mcu_lsu_req | axi_mcu_ifu_req) & patch_rd_open;

assign filter_error = cif_resp_if.dv & ~(wr_filter_success | rd_filter_success);

///////////////////////////////////////////////
// Sticky patch flag (cold reset only)
///////////////////////////////////////////////

always_ff @(posedge clk or negedge mci_pwrgood) begin
    if (!mci_pwrgood) begin
        mcu_rom_patch_active_o <= 1'b0;
    end
    else if (sram_write_req) begin
        mcu_rom_patch_active_o <= 1'b1;
    end
end

///////////////////////////////////////////////
// SRAM request
///////////////////////////////////////////////

// Reads take 2 clock cycles (1 cycle SRAM latency). Writes take 1.
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        sram_req_second_cycle <= 1'b0;
    end
    else begin
        sram_req_second_cycle <= rd_filter_success & ~sram_req_second_cycle;
    end
end

assign sram_write_req       = wr_filter_success;
assign sram_read_req        = rd_filter_success & ~sram_req_second_cycle;
assign sram_read_data_avail = sram_req_second_cycle;

assign mci_mcu_rom_patch_sram_req_if.req.cs   = sram_write_req | sram_read_req;
assign mci_mcu_rom_patch_sram_req_if.req.we   = sram_write_req;
assign mci_mcu_rom_patch_sram_req_if.req.addr = (sram_write_req | sram_read_req) ?
                                                cif_resp_if.req_data.addr[MCU_ROM_PATCH_SRAM_CIF_ADDR_W-1:2] : '0;
assign mci_mcu_rom_patch_sram_req_if.req.wdata.data = sram_write_req ? cif_resp_if.req_data.wdata : '0;

// From RISC-V core beh_lib.sv (32-bit data, 7-bit ECC)
rvecc_encode ecc_encode (
    .din    (mci_mcu_rom_patch_sram_req_if.req.wdata.data),
    .ecc_out(mci_mcu_rom_patch_sram_req_if.req.wdata.ecc )
);

///////////////////////////////////////////////
// Read response
///////////////////////////////////////////////

assign sram_rdata     = mci_mcu_rom_patch_sram_req_if.resp.rdata.data;
assign sram_rdata_ecc = mci_mcu_rom_patch_sram_req_if.resp.rdata.ecc;

rvecc_decode ecc_decode (
    .en              (sram_read_data_avail ),
    .sed_ded         (1'b0                 ), // Correct single-bit, detect double-bit
    .din             (sram_rdata           ),
    .ecc_in          (sram_rdata_ecc       ),
    .dout            (sram_rdata_cor       ),
    .ecc_out         (                     ),
    .single_ecc_error(sram_single_ecc_error),
    .double_ecc_error(sram_double_ecc_error)
);

assign cif_resp_if.rdata    = sram_read_data_avail ? sram_rdata_cor : '0;
assign cif_resp_if.req_hold = sram_read_req;
assign cif_resp_if.error    = filter_error | sram_double_ecc_error;

///////////////////////////////////////////////
// Assertions
///////////////////////////////////////////////

// Single-port SRAM
`CALIPTRA_ASSERT_MUTEX(ERR_MCU_ROM_PATCH_SRAM_MULTI_REQ, {sram_write_req, sram_read_req}, clk, !rst_b)

// Patch can only be loaded while Caliptra core is in reset and patching is permitted
`CALIPTRA_ASSERT(McuRomPatchWrOnlyCptraInReset_A, sram_write_req |-> (!cptra_rst_b && !cptra_core_rst_b_i && !cptra_released_q), clk, !rst_b)
`CALIPTRA_ASSERT(McuRomPatchWrOnlyLcAllowed_A, sram_write_req |-> lc_patch_allowed, clk, !rst_b)

// Patch can only be fetched/read after it was loaded this power cycle
`CALIPTRA_ASSERT(McuRomPatchRdOnlyWhenActive_A, sram_read_req |-> mcu_rom_patch_active_o, clk, !rst_b)

// Patch flag is sticky until cold reset
`CALIPTRA_ASSERT(McuRomPatchActiveSticky_A, mcu_rom_patch_active_o |=> mcu_rom_patch_active_o, clk, !mci_pwrgood)

// SRAM ECC errors
`CALIPTRA_ASSERT_NEVER(ERR_MCU_ROM_PATCH_SRAM_ECC_DB_ERROR, sram_double_ecc_error, clk, !rst_b)
`CALIPTRA_ASSERT_NEVER(ERR_MCU_ROM_PATCH_SRAM_ECC_SB_ERROR, sram_single_ecc_error, clk, !rst_b)

endmodule
