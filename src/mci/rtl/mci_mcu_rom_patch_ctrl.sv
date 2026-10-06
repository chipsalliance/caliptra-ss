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
//      fetches patch instructions from it. On devices that did not load a patch,
//      the SRAM becomes general purpose data memory once MCU RT FW is running.
//
//      Security rules (all enforced in HW):
//      Patch write : MCU LSU only, full-word only, strictly sequential from the
//                    SRAM base (write pointer), and only while
//                      - LC state is TEST_LOCKED0-6, TEST_UNLOCKED0-7 or DEV
//                        (valid, no fatal LC error)
//                      - Caliptra core has not left reset yet in this power
//                        cycle, both at the MCI boot sequencer and at the
//                        Caliptra core reset input
//      Patch read  : MCU LSU/IFU only, only below the write pointer (words
//                    written by MCU ROM in this power cycle), and only while the
//                    LC condition above still holds. Stale or preloaded SRAM
//                    content is never fetchable. Allowed for both MCU ROM and
//                    MCU RT FW, and across warm resets, so MCU ROM does not
//                    reload the patch after a warm reset and MCU RT FW can call
//                    patched ROM functions.
//      Patch flag  : mcu_rom_patch_active_o = (write pointer != 0). The write
//                    pointer and flag are cleared only by a cold reset
//                    (mci_pwrgood), not by warm reset. Readable in
//                    HW_FLOW_STATUS.mcu_rom_patch_active. Stable before Caliptra
//                    core leaves reset. Blocks UDS/FE provisioning in the fuse
//                    controller filter and zeroizes the UDS/FE delivered to
//                    Caliptra core.
//      Release     : If no patch was loaded in this power cycle, once MCU RT FW
//                    is running (MCU released from reset with the FW exec region
//                    locked) any AXI user may read/write the SRAM as data. Never
//                    fetchable while released. Cleared by warm reset, so every
//                    MCU ROM run starts with the SRAM closed.
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

    // MCU reset and FW exec region lock, to detect MCU RT FW
    input logic mcu_rst_b,
    input logic mcu_sram_fw_exec_region_lock,

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

localparam MCU_ROM_PATCH_SRAM_IF_ADDR_W = $bits(mci_mcu_rom_patch_sram_req_if.req.addr);

logic otp_state_valid_q;
logic cptra_released_q;
logic lc_patch_allowed;
logic patch_wr_open;
logic patch_rd_open;

logic [MCU_ROM_PATCH_SRAM_ADDR_W:0]   write_ptr;
logic [MCU_ROM_PATCH_SRAM_ADDR_W-1:0] req_word_addr;
logic                                 req_full_word;
logic                                 req_in_order;
logic                                 req_in_patch;

logic mcu_rst_b_q;
logic mcu_rt_running;
logic released;

logic patch_wr_success;
logic patch_rd_success;
logic rel_wr_success;
logic rel_rd_success;
logic rd_filter_success;
logic rmw_req;
logic filter_error;

logic sram_req_second_cycle;
logic sram_read_req;
logic sram_write_req;
logic sram_read_data_avail;

logic [MCU_ROM_PATCH_SRAM_DATA_W-1:0]     sram_rdata;
logic [MCU_ROM_PATCH_SRAM_DATA_W-1:0]     sram_rdata_cor;
logic [MCU_ROM_PATCH_SRAM_DATA_W-1:0]     sram_rmw_wdata;
logic [MCU_ROM_PATCH_SRAM_ECC_DATA_W-1:0] sram_rdata_ecc;

///////////////////////////////////////////////
// LC gate
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
assign lc_patch_allowed = otp_state_valid_q && !lc_fatal_state_error_i &&
                          ((otp_static_state_i == lc_ctrl_state_pkg::LcStTestLocked0) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestLocked1) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestLocked2) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestLocked3) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestLocked4) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestLocked5) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestLocked6) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked0) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked1) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked2) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked3) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked4) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked5) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked6) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStTestUnlocked7) ||
                           (otp_static_state_i == lc_ctrl_state_pkg::LcStDev));

///////////////////////////////////////////////
// Patch window
///////////////////////////////////////////////

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

// Closed once MCU RT FW runs, so a released data write never counts as a patch write.
assign patch_wr_open = lc_patch_allowed & ~cptra_rst_b & ~cptra_core_rst_b_i & ~cptra_released_q & ~mcu_rt_running;
assign patch_rd_open = lc_patch_allowed & mcu_rom_patch_active_o;

// Patch words must be written in order from the SRAM base. Only words written
// by MCU ROM in this power cycle (below the write pointer) can be read/fetched.
assign req_word_addr = cif_resp_if.req_data.addr[MCU_ROM_PATCH_SRAM_CIF_ADDR_W-1:2];
assign req_full_word = &cif_resp_if.req_data.wstrb;
assign req_in_order  = ({1'b0, req_word_addr} == write_ptr);
assign req_in_patch  = ({1'b0, req_word_addr} <  write_ptr);

always_ff @(posedge clk or negedge mci_pwrgood) begin
    if (!mci_pwrgood) begin
        write_ptr <= '0;
    end
    else if (patch_wr_success) begin
        write_ptr <= write_ptr + 1'b1;
    end
end

assign mcu_rom_patch_active_o = |write_ptr;

///////////////////////////////////////////////
// Release to SoC once MCU RT FW is running
///////////////////////////////////////////////

// MCU is released from reset with the FW exec region locked only after Caliptra
// core loaded MCU RT FW, i.e. MCU ROM is done. Warm reset clears it.
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        mcu_rst_b_q    <= 1'b0;
        mcu_rt_running <= 1'b0;
    end
    else begin
        mcu_rst_b_q <= mcu_rst_b;
        if (mcu_rst_b && !mcu_rst_b_q && mcu_sram_fw_exec_region_lock) begin
            mcu_rt_running <= 1'b1;
        end
    end
end

// A loaded patch must survive warm resets for MCU ROM, so it is never released.
assign released = mcu_rt_running & ~mcu_rom_patch_active_o;

///////////////////////////////////////////////
// Access filter
///////////////////////////////////////////////

assign patch_wr_success = cif_resp_if.dv &  cif_resp_if.req_data.write & axi_mcu_lsu_req &
                          req_full_word & req_in_order & patch_wr_open;
assign patch_rd_success = cif_resp_if.dv & ~cif_resp_if.req_data.write &
                          (axi_mcu_lsu_req | axi_mcu_ifu_req) & req_in_patch & patch_rd_open;

// Released: any AXI user, data only (no instruction fetch).
assign rel_wr_success = cif_resp_if.dv &  cif_resp_if.req_data.write & released;
assign rel_rd_success = cif_resp_if.dv & ~cif_resp_if.req_data.write & released & ~axi_mcu_ifu_req;

assign rd_filter_success = patch_rd_success | rel_rd_success;
assign rmw_req           = rel_wr_success & ~req_full_word;

assign filter_error = cif_resp_if.dv & ~(patch_wr_success | patch_rd_success | rel_wr_success | rel_rd_success);

///////////////////////////////////////////////
// SRAM request
///////////////////////////////////////////////

// Reads and partial writes (RMW) take 2 clock cycles (1 cycle SRAM latency).
// Full-word writes take 1.
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        sram_req_second_cycle <= 1'b0;
    end
    else begin
        sram_req_second_cycle <= (rd_filter_success | rmw_req) & ~sram_req_second_cycle;
    end
end

assign sram_read_req        = (rd_filter_success | rmw_req) & ~sram_req_second_cycle;
assign sram_write_req       = patch_wr_success | (rel_wr_success & req_full_word) |
                              (rmw_req & sram_req_second_cycle & ~sram_double_ecc_error);
assign sram_read_data_avail = sram_req_second_cycle;

genvar i;
generate
    for (i = 0; i < MCU_ROM_PATCH_SRAM_DATA_W_BYTES; i = i + 1) begin : gen_rmw_data
        assign sram_rmw_wdata[i*8 +: 8] = cif_resp_if.req_data.wstrb[i] ? cif_resp_if.req_data.wdata[i*8 +: 8] :
                                                                          sram_rdata_cor[i*8 +: 8];
    end
endgenerate

assign mci_mcu_rom_patch_sram_req_if.req.cs   = sram_write_req | sram_read_req;
assign mci_mcu_rom_patch_sram_req_if.req.we   = sram_write_req;
assign mci_mcu_rom_patch_sram_req_if.req.addr[MCU_ROM_PATCH_SRAM_ADDR_W-1:0] = (sram_write_req | sram_read_req) ? req_word_addr : '0;

generate
    if (MCU_ROM_PATCH_SRAM_IF_ADDR_W > MCU_ROM_PATCH_SRAM_ADDR_W) begin : gen_addr_tie_off
        // Upper address bits are 0 since the SRAM is smaller than the addressable space
        assign mci_mcu_rom_patch_sram_req_if.req.addr[MCU_ROM_PATCH_SRAM_IF_ADDR_W-1:MCU_ROM_PATCH_SRAM_ADDR_W] = '0;
    end
endgenerate

assign mci_mcu_rom_patch_sram_req_if.req.wdata.data = ~sram_write_req ? '0             :
                                                      rmw_req         ? sram_rmw_wdata :
                                                                        cif_resp_if.req_data.wdata;

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

assign cif_resp_if.rdata    = (sram_read_data_avail & ~cif_resp_if.req_data.write) ? sram_rdata_cor : '0;
assign cif_resp_if.req_hold = sram_read_req;
assign cif_resp_if.error    = filter_error | sram_double_ecc_error;

///////////////////////////////////////////////
// Assertions
///////////////////////////////////////////////

// Single-port SRAM
`CALIPTRA_ASSERT_MUTEX(ERR_MCU_ROM_PATCH_SRAM_MULTI_REQ, {sram_write_req, sram_read_req}, clk, !rst_b)

// Patch can only be loaded in order, while Caliptra core is in reset and patching is permitted
`CALIPTRA_ASSERT(McuRomPatchWrOnlyCptraInReset_A, patch_wr_success |-> (!cptra_rst_b && !cptra_core_rst_b_i && !cptra_released_q), clk, !rst_b)
`CALIPTRA_ASSERT(McuRomPatchWrOnlyLcAllowed_A, patch_wr_success |-> lc_patch_allowed, clk, !rst_b)
`CALIPTRA_ASSERT(McuRomPatchWrInOrder_A, patch_wr_success |-> req_in_order, clk, !rst_b)

// Instruction fetch only from words loaded by MCU ROM this power cycle
`CALIPTRA_ASSERT(McuRomPatchFetchOnlyPatch_A, (sram_read_req && axi_mcu_ifu_req && !cif_resp_if.req_data.write) |-> (patch_rd_open && req_in_patch), clk, !rst_b)

// Never released while a patch is loaded, and the patch window is closed while released
`CALIPTRA_ASSERT(McuRomPatchNoReleaseWhenPatched_A, released |-> !mcu_rom_patch_active_o, clk, !rst_b)
`CALIPTRA_ASSERT(McuRomPatchNoPatchWrWhenReleased_A, released |-> !patch_wr_open, clk, !rst_b)

// Patch flag is sticky until cold reset
`CALIPTRA_ASSERT(McuRomPatchActiveSticky_A, mcu_rom_patch_active_o |=> mcu_rom_patch_active_o, clk, !mci_pwrgood)

// SRAM ECC errors
`CALIPTRA_ASSERT_NEVER(ERR_MCU_ROM_PATCH_SRAM_ECC_DB_ERROR, sram_double_ecc_error, clk, !rst_b)
`CALIPTRA_ASSERT_NEVER(ERR_MCU_ROM_PATCH_SRAM_ECC_SB_ERROR, sram_single_ecc_error, clk, !rst_b)

endmodule
