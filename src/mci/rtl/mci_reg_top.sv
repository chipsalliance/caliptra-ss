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

`include "mci_reg_defines.svh"

module mci_reg_top 
    import mci_reg_pkg::*;
    #(
    )
    (
    input logic clk,

    // Resets
    input logic mci_rst_b,
    input logic mcu_rst_b,
    input logic mci_pwrgood,

    // REG HWIF signals
    output mci_reg__out_t mci_reg_hwif_out,

    // AXI Privileged requests
    input logic clp_req,
    input logic mcu_req,

    // WDT specific signals
    output logic wdt_timer1_timeout_serviced,
    output logic wdt_timer2_timeout_serviced,
    input  logic t1_timeout,
    input  logic t2_timeout,
    input  logic t1_timeout_p,
    input  logic t2_timeout_p,
    
    // Generic in/out
    input  logic [63:0] mci_generic_input_wires,
    output logic [63:0] mci_generic_output_wires,

    // SS error signals
    input logic [31:0] agg_error_fatal,
    input logic [31:0] agg_error_non_fatal,

    // SOC Interrupts
    output logic mci_error_fatal,
    output logic mci_error_non_fatal,

    // MCU interrupts
    output logic mcu_timer_int,
    output logic mci_intr,

    // Straps

    // MCU Reset vector
    input  logic [31:0] strap_mcu_reset_vector, // default reset vector
    output logic [31:0] mcu_reset_vector,       // reset vector used by MCU

    // NMI
    input  logic nmi_intr,
    output logic [31:0] mcu_nmi_vector,

    // MISC 
    input logic mcu_sram_fw_exec_region_lock,

    // MCU SRAM specific signals
    input logic mcu_sram_single_ecc_error,
    input logic mcu_sram_double_ecc_error,

    // Reset status
    input  logic mcu_reset_once,
    input  logic fw_boot_upd_reset,     // First MCU reset request
    input  logic fw_hitless_upd_reset,  // Other MCU reset requests

    
    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if

    );

// Reset reason
logic pwrgood_toggle_hint;
logic Warm_Reset_Capture_Flag;

// Interrupts 
logic mci_error_intr;
logic mci_notif_intr;

// Error signals
logic mci_reg_read_error;
logic mci_reg_write_error;
logic unmasked_hw_error_fatal_write;
logic unmasked_agg_error_fatal_write;
logic unmasked_hw_error_non_fatal_write; 
logic unmasked_hw_error_non_fatal_is_set; 
logic unmasked_agg_error_non_fatal_write; 
logic unmasked_agg_error_non_fatal_is_set; 
logic [31:0] agg_error_fatal_sync;
logic [31:0] agg_error_non_fatal_sync;

// REG HWIF signals
mci_reg__in_t   mci_reg_hwif_in;

// WDT signals
logic   error_wdt_timer1_timeout_sts_prev;
logic   error_wdt_timer2_timeout_sts_prev;

// Byte Enable mapping
logic [MCI_REG_DATA_WIDTH-1:0] c_cpuif_wr_biten;

// MCU Reset Request interrupt 
logic cptra_mcu_rst_req;
logic mcu_sram_fw_exec_region_lock_posedge;
logic mcu_sram_fw_exec_region_lock_negedge;
logic mcu_sram_fw_exec_region_lock_prev;

// Fuse write done
logic strap_we;

///////////////////////////////////////////////
// Sync to signals to local clock domain
///////////////////////////////////////////////

caliptra_prim_flop_2sync #(
  .Width(32)
) u_prim_flop_2sync_agg_error_fatal (
  .clk_i(clk),
  .rst_ni(mci_pwrgood),
  .d_i(agg_error_fatal),
  .q_o(agg_error_fatal_sync));

caliptra_prim_flop_2sync #(
  .Width(32)
) u_prim_flop_2sync_agg_error_non_fatal (
  .clk_i(clk),
  .rst_ni(mci_pwrgood),
  .d_i(agg_error_non_fatal),
  .q_o(agg_error_non_fatal_sync));

///////////////////////////////////////////////
// Map CIF WSTRB to BITEN of CSR block
///////////////////////////////////////////////
genvar i;
generate 
    for (i = 0; i < MCI_REG_DATA_WIDTH; i = i + 1) begin : map_wstrb_to_biten
        assign c_cpuif_wr_biten[i] = cif_resp_if.req_data.wstrb[i/8];
    end
endgenerate

///////////////////////////////////////////////
// GENERIC Wires        
///////////////////////////////////////////////
caliptra_prim_flop_2sync #(
  .Width(64)
) u_prim_flop_2sync_mcu_sram_fw_exec_region_lock (
  .clk_i(clk),
  .rst_ni(mci_rst_b),
  .d_i(mci_generic_input_wires),
  .q_o({mci_reg_hwif_in.GENERIC_INPUT_WIRES[1].wires.next, mci_reg_hwif_in.GENERIC_INPUT_WIRES[0].wires.next}));

assign mci_generic_output_wires = {mci_reg_hwif_out.GENERIC_OUTPUT_WIRES[1].wires.value, mci_reg_hwif_out.GENERIC_OUTPUT_WIRES[0].wires.value};

///////////////////////////////////////////////
// Error handling logic
///////////////////////////////////////////////

assign cif_resp_if.error = mci_reg_read_error | mci_reg_write_error;

///////////////////////////////////////////////
// Hold response logic
///////////////////////////////////////////////

// Reads and writes occur in 1 clock cycles
assign cif_resp_if.hold = '0;

///////////////////////////////////////////////
// STRAPS / FUSE WR DONE       
///////////////////////////////////////////////

// Fuse write done can be written by MCU if it is already NOT '1.
// The bit gets reset on cold reset
always_comb mci_reg_hwif_in.FUSE_WR_DONE.done.swwe = (mcu_req & cif_resp_if.dv) & ~mci_reg_hwif_out.FUSE_WR_DONE.done.value;

// Subsystem straps capture the initial value from input port on rising edge of cptra_pwrgood
always_ff @(posedge clk or negedge mci_pwrgood) begin
     if(~mci_pwrgood) begin
        strap_we <= 1'b1;
    end
    else begin
        strap_we <= 1'b0;
    end
end
  
// Value
// FIXME always_comb begin
// FIXME     for (int i=0; i<8; i++) begin
// FIXME         for (int j=0; j<12; j++) begin
// FIXME             mci_reg_hwif_in.PROD_DEBUG_UNLOCK_PK_HASH_REG[i][j].hash.next = strap_prod_debug_unlock_pk_hash[i][j];
// FIXME         end
// FIXME     end
// FIXME end
// FIXME 
// FIXME // Write enable
// FIXME always_comb begin
// FIXME     for (int i=0; i<8; i++) begin
// FIXME         for (int j=0; j<12; j++) begin
// FIXME             mci_reg_hwif_in.PROD_DEBUG_UNLOCK_PK_HASH_REG[i][j].hash.we = strap_we;
// FIXME         end
// FIXME     end
// FIXME end
// FIXME 
// FIXME 
// FIXME 
// FIXME // Locking
// FIXME always_comb begin
// FIXME     for (int i=0; i<8; i++) begin
// FIXME         for (int j=0; j<12; j++) begin
// FIXME             mci_reg_hwif_in.PROD_DEBUG_UNLOCK_PK_HASH_REG[i][j].hash.swwel = mci_reg_hwif_out.FUSE_WR_DONE.done.value ;
// FIXME         end
// FIXME     end
// FIXME end

///////////////////////////////////////////////
// TEMP CONNECTIONS FIXME
///////////////////////////////////////////////

// Resets
assign mci_reg_hwif_in.mci_rst_b = mci_rst_b;
assign mci_reg_hwif_in.mcu_rst_b = mcu_rst_b; // FIXME is this really required?
assign mci_reg_hwif_in.mci_pwrgood = mci_pwrgood;

// Agent requests
assign mci_reg_hwif_in.cptra_req    = clp_req; 
assign mci_reg_hwif_in.mcu_req      = mcu_req;



assign mci_reg_hwif_in.CAPABILITIES = '0; // FIXME
assign mci_reg_hwif_in.HW_REV_ID = '0; // FIXME
assign mci_reg_hwif_in.HW_CONFIG = '0; // FIXME
assign mci_reg_hwif_in.FLOW_STATUS = '0; // FIXME

assign mci_reg_hwif_in.PROD_DEBUG_UNLOCK_PK_HASH_REG = '0; // FIXME
assign mci_reg_hwif_in.FW_SRAM_EXEC_REGION_SIZE = '0; // FIXME
assign mci_reg_hwif_in.STICKY_DATA_VAULT_CTRL = '0; // FIXME
assign mci_reg_hwif_in.STICKY_DATA_VAULT_ENTRY = '0; // FIXME
assign mci_reg_hwif_in.DATA_VAULT_CTRL = '0; // FIXME
assign mci_reg_hwif_in.DATA_VAULT_ENTRY = '0; // FIXME
assign mci_reg_hwif_in.STICKY_LOCKABLE_SCRATCH_REG_CTRL = '0; // FIXME
assign mci_reg_hwif_in.STICKY_LOCKABLE_SCRATCH_REG = '0; // FIXME
assign mci_reg_hwif_in.LOCKABLE_SCRATCH_REG_CTRL = '0; // FIXME
assign mci_reg_hwif_in.LOCKABLE_SCRATCH_REG = '0; // FIXME

// mtime always increments, but if it's being written by software the write
// value will update the register. Deasserting incr in this case prevents the
// SW write from being dropped (due to RDL compiler failing to give SW precedence properly).
assign mci_reg_hwif_in.MCU_RV_MTIME_L.count_l.incr = !(cif_resp_if.dv && mci_reg_hwif_out.MCU_RV_MTIME_L.count_l.swmod);
assign mci_reg_hwif_in.MCU_RV_MTIME_H.count_h.incr = !(cif_resp_if.dv && mci_reg_hwif_out.MCU_RV_MTIME_H.count_h.swmod) && mci_reg_hwif_out.MCU_RV_MTIME_L.count_l.overflow;
assign mcu_timer_int  =  {mci_reg_hwif_out.MCU_RV_MTIME_H.count_h.value     ,mci_reg_hwif_out.MCU_RV_MTIME_L.count_l.value}
                     >=
                     {mci_reg_hwif_out.MCU_RV_MTIMECMP_H.compare_h.value,mci_reg_hwif_out.MCU_RV_MTIMECMP_L.compare_l.value};

///////////////////////////////////////////////
// MCU Reset Request interrupt 
///////////////////////////////////////////////


always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mcu_sram_fw_exec_region_lock_prev <= 0;
    end
    else if(!Warm_Reset_Capture_Flag) begin
        mcu_sram_fw_exec_region_lock_prev <= mcu_sram_fw_exec_region_lock;
    end
end

assign mcu_sram_fw_exec_region_lock_posedge = mcu_sram_fw_exec_region_lock & (~mcu_sram_fw_exec_region_lock_prev);
assign mcu_sram_fw_exec_region_lock_negedge = (~mcu_sram_fw_exec_region_lock) & mcu_sram_fw_exec_region_lock_prev;

// On first boot (mcu_reset_once) we expect region_lock to transition 0->1 indicating 
// a FW update is available for MCU. This will trigger MCU ROM to reset itself.
// On all subsequence update (hitless FW Update) we expect region_lock to go 1->0
// which will trigger MCU RT FW to be interrupted and reset itself. While the MCU
// is in reset and the FW image is in MCU SRAM the region_lock will be set 0->1
// in the boot sequencer this is when MCU is brought out of reset.
always_comb begin
    if(!mcu_reset_once && mcu_sram_fw_exec_region_lock_posedge) begin
        cptra_mcu_rst_req = 1'b1;
    end
    else if(mcu_sram_fw_exec_region_lock_negedge) begin
        cptra_mcu_rst_req = 1'b1;
    end
    else begin
        cptra_mcu_rst_req = 1'b0;
    end
end

assign mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_clpra_mcu_reset_req_sts.hwset = cptra_mcu_rst_req;

///////////////////////////////////////////////
// MCI Interrupt aggregation
///////////////////////////////////////////////
assign mci_error_intr = mci_reg_hwif_out.intr_block_rf.error_global_intr_r.intr;
assign mci_notif_intr = mci_reg_hwif_out.intr_block_rf.notif_global_intr_r.intr;


always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mci_intr <= 0;
    end
    else  begin
        mci_intr <= mci_error_intr | mci_notif_intr;
    end
end

///////////////////////////////////////////////
// MCU Reset Request
///////////////////////////////////////////////
assign mci_reg_hwif_in.RESET_REQUEST.mcu_req.hwclr = ~mcu_rst_b;

///////////////////////////////////////////////
// Reset reason
///////////////////////////////////////////////

assign mci_reg_hwif_in.RESET_REASON.FW_BOOT_UPD_RESET.next = fw_boot_upd_reset; 

assign mci_reg_hwif_in.RESET_REASON.FW_HITLESS_UPD_RESET.next = fw_hitless_upd_reset; 

// pwrgood_hint informs if the powergood toggled
always_ff @(posedge clk or negedge mci_pwrgood) begin
     if(~mci_pwrgood) begin
        pwrgood_toggle_hint <= 1;
     end
     // Reset the bit after warm reset deassertion has been observed
     else if(Warm_Reset_Capture_Flag) begin
        pwrgood_toggle_hint <= 0;
     end
end

always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        Warm_Reset_Capture_Flag <= 0;
    end
    else if(!Warm_Reset_Capture_Flag) begin
        Warm_Reset_Capture_Flag <= 1;
    end
end

// PwrGood is used to decide if the warm reset toggle happened due to pwrgood or
// only due to warm reset. We also need to clear this bit when its
// FW_*_UPD_RESET only path
always_comb begin
    if (!Warm_Reset_Capture_Flag) begin
         mci_reg_hwif_in.RESET_REASON.WARM_RESET.next = ~pwrgood_toggle_hint;
    end
    else if (mci_reg_hwif_out.RESET_REASON.FW_BOOT_UPD_RESET.value || mci_reg_hwif_out.RESET_REASON.FW_HITLESS_UPD_RESET.value) begin
         mci_reg_hwif_in.RESET_REASON.WARM_RESET.next = 1'b0;
    end 
    else begin
         mci_reg_hwif_in.RESET_REASON.WARM_RESET.next = mci_reg_hwif_out.RESET_REASON.WARM_RESET.value;
    end
end


///////////////////////////////////////////////
// MCI RESET Vector
///////////////////////////////////////////////
assign mci_reg_hwif_in.MCU_RESET_VECTOR.vec.next = strap_mcu_reset_vector; 
assign mci_reg_hwif_in.MCU_RESET_VECTOR.vec.we = pwrgood_toggle_hint; // FIXME is there more logic needed for DMI or security? 

assign mcu_reset_vector = mci_reg_hwif_out.MCU_RESET_VECTOR.vec.value;

///////////////////////////////////////////////
// NMI Vector   
///////////////////////////////////////////////
assign mcu_nmi_vector = mci_reg_hwif_out.MCU_NMI_VECTOR.vec; // FIXME reset for this? MCI reset 

////////////////////////////////////////////////////////
// Write-enables for HW_ERROR_FATAL and HW_ERROR_NON_FATAL
// Also calculate whether or not an unmasked event is being set, so we can
// trigger the SOC interrupt signal
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.we  = mcu_sram_double_ecc_error; // FIXME do we need to add a reset window disable like in caliptra?
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .we      = nmi_intr;
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 FATAL events)
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.next    = 1'b1;
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .next        = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_hw_error_fatal_write = (mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .we      && ~mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_nmi_pin.value && |mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .next) ||
                                            (mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.we  && ~mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_ecc_unc.value && |mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.next);

////////////////////////////////////////////////////////
// Write-enables for HW_ERROR_FATAL and HW_ERROR_NON_FATAL
// Also calculate whether or not an unmasked event is being set, so we can
// trigger the SOC interrupt signal
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal0.we  = agg_error_fatal_sync[0];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal1.we  = agg_error_fatal_sync[1];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal2.we  = agg_error_fatal_sync[2];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal3.we  = agg_error_fatal_sync[3];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal4.we  = agg_error_fatal_sync[4];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal5.we  = agg_error_fatal_sync[5];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal6.we  = agg_error_fatal_sync[6];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal7.we  = agg_error_fatal_sync[7];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal8.we  = agg_error_fatal_sync[8];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal9.we  = agg_error_fatal_sync[9];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal10.we  = agg_error_fatal_sync[10];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal11.we  = agg_error_fatal_sync[11];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal12.we  = agg_error_fatal_sync[12];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal13.we  = agg_error_fatal_sync[13];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal14.we  = agg_error_fatal_sync[14];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal15.we  = agg_error_fatal_sync[15];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal16.we  = agg_error_fatal_sync[16];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal17.we  = agg_error_fatal_sync[17];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal18.we  = agg_error_fatal_sync[18];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal19.we  = agg_error_fatal_sync[19];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal20.we  = agg_error_fatal_sync[20];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal21.we  = agg_error_fatal_sync[21];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal22.we  = agg_error_fatal_sync[22];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal23.we  = agg_error_fatal_sync[23];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal24.we  = agg_error_fatal_sync[24];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal25.we  = agg_error_fatal_sync[25];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal26.we  = agg_error_fatal_sync[26];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal27.we  = agg_error_fatal_sync[27];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal28.we  = agg_error_fatal_sync[28];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal29.we  = agg_error_fatal_sync[29];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal30.we  = agg_error_fatal_sync[30];
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal31.we  = agg_error_fatal_sync[31];
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 FATAL events)
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal0.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal1.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal2.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal3.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal4.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal5.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal6.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal7.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal8.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal9.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal10.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal11.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal12.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal13.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal14.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal15.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal16.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal17.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal18.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal19.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal20.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal21.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal22.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal23.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal24.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal25.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal26.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal27.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal28.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal29.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal30.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal31.next = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_agg_error_fatal_write = (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal0.we          && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal0       && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal0.next) ||
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal1.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal1     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal1.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal2.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal2     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal2.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal3.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal3     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal3.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal4.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal4     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal4.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal5.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal5     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal5.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal6.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal6     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal6.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal7.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal7     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal7.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal8.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal8     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal8.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal9.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal9     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal9.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal10.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal10     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal10.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal11.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal11     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal11.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal12.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal12     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal12.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal13.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal13     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal13.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal14.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal14     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal14.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal15.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal15     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal15.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal16.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal16     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal16.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal17.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal17     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal17.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal18.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal18     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal18.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal19.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal19     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal19.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal20.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal20     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal20.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal21.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal21     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal21.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal22.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal22     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal22.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal23.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal23     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal23.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal24.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal24     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal24.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal25.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal25     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal25.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal26.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal26     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal26.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal27.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal27     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal27.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal28.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal28     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal28.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal29.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal29     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal29.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal30.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal30     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal30.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal31.we   && ~mci_reg_hwif_out.internal_agg_error_fatal_mask.mask_agg_error_fatal31     && |mci_reg_hwif_in.AGG_ERROR_FATAL.agg_error_fatal31.next)  
                                             ;
                                              
                                              
                                              


always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.RSVD.we = '0; // FIXME remove
// FIXME always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_no_lock.we = mbox_protocol_error.axs_without_lock;
// FIXME always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_ooo    .we = mbox_protocol_error.axs_incorrect_order;
// FIXME always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_ecc_unc     .we = sram_double_ecc_error;
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 NON-FATAL events)
always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.RSVD.next = 1'b1; // FIXME remove
// FIXME always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_no_lock.next = 1'b1;
// FIXME always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_ooo    .next = 1'b1;
// FIXME always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_ecc_unc     .next = 1'b1;
// FIXME always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.rsvd.next[28:0]        = 29'h0;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_hw_error_non_fatal_write = '0; // FIXME 
                                                // FIXME (mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_no_lock.we && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_no_lock.value && |soc_ifc_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_no_lock.next) ||
                                                // FIXME (mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_ooo    .we && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_ooo    .value && |soc_ifc_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_prot_ooo    .next) ||
                                                // FIXME (mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_ecc_unc     .we && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_ecc_unc     .value && |soc_ifc_reg_hwif_in.HW_ERROR_NON_FATAL.mbox_ecc_unc     .next);
always_comb unmasked_hw_error_non_fatal_is_set = '0; // FIXME 
                                                 // FIXME (mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox_prot_no_lock.value && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_no_lock.value) ||
                                                 // FIXME (mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox_prot_ooo    .value && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_ooo    .value) ||
                                                 // FIXME (mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox_ecc_unc     .value && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_ecc_unc     .value);

always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal0.we  = agg_error_non_fatal_sync[0];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal1.we  = agg_error_non_fatal_sync[1];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal2.we  = agg_error_non_fatal_sync[2];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal3.we  = agg_error_non_fatal_sync[3];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal4.we  = agg_error_non_fatal_sync[4];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal5.we  = agg_error_non_fatal_sync[5];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal6.we  = agg_error_non_fatal_sync[6];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal7.we  = agg_error_non_fatal_sync[7];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal8.we  = agg_error_non_fatal_sync[8];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal9.we  = agg_error_non_fatal_sync[9];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal10.we  = agg_error_non_fatal_sync[10];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal11.we  = agg_error_non_fatal_sync[11];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal12.we  = agg_error_non_fatal_sync[12];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal13.we  = agg_error_non_fatal_sync[13];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal14.we  = agg_error_non_fatal_sync[14];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal15.we  = agg_error_non_fatal_sync[15];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal16.we  = agg_error_non_fatal_sync[16];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal17.we  = agg_error_non_fatal_sync[17];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal18.we  = agg_error_non_fatal_sync[18];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal19.we  = agg_error_non_fatal_sync[19];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal20.we  = agg_error_non_fatal_sync[20];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal21.we  = agg_error_non_fatal_sync[21];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal22.we  = agg_error_non_fatal_sync[22];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal23.we  = agg_error_non_fatal_sync[23];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal24.we  = agg_error_non_fatal_sync[24];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal25.we  = agg_error_non_fatal_sync[25];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal26.we  = agg_error_non_fatal_sync[26];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal27.we  = agg_error_non_fatal_sync[27];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal28.we  = agg_error_non_fatal_sync[28];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal29.we  = agg_error_non_fatal_sync[29];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal30.we  = agg_error_non_fatal_sync[30];
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal31.we  = agg_error_non_fatal_sync[31];
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 NON_FATAL events)
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal0.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal1.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal2.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal3.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal4.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal5.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal6.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal7.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal8.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal9.next  = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal10.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal11.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal12.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal13.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal14.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal15.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal16.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal17.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal18.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal19.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal20.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal21.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal22.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal23.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal24.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal25.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal26.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal27.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal28.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal29.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal30.next = 1'b1;
always_comb mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal31.next = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_agg_error_non_fatal_write = (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal0.we          && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal0       && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal0.next) ||
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal1.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal1     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal1.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal2.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal2     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal2.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal3.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal3     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal3.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal4.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal4     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal4.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal5.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal5     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal5.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal6.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal6     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal6.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal7.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal7     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal7.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal8.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal8     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal8.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal9.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal9     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal9.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal10.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal10     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal10.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal11.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal11     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal11.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal12.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal12     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal12.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal13.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal13     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal13.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal14.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal14     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal14.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal15.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal15     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal15.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal16.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal16     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal16.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal17.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal17     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal17.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal18.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal18     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal18.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal19.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal19     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal19.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal20.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal20     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal20.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal21.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal21     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal21.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal22.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal22     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal22.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal23.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal23     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal23.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal24.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal24     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal24.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal25.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal25     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal25.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal26.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal26     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal26.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal27.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal27     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal27.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal28.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal28     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal28.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal29.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal29     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal29.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal30.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal30     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal30.next) ||  
                                             (mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal31.we   && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal31     && |mci_reg_hwif_in.AGG_ERROR_NON_FATAL.agg_error_non_fatal31.next)  
                                             ;
always_comb unmasked_agg_error_non_fatal_is_set = (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal0.value  && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal0.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal1.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal1.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal2.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal2.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal3.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal3.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal4.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal4.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal5.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal5.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal6.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal6.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal7.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal7.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal8.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal8.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal9.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal9.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal10.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal10.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal11.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal11.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal12.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal12.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal13.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal13.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal14.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal14.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal15.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal15.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal16.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal16.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal17.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal17.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal18.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal18.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal19.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal19.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal20.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal20.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal21.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal21.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal22.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal22.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal23.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal23.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal24.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal24.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal25.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal25.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal26.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal26.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal27.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal27.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal28.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal28.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal29.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal29.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal30.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal30.value) ||
                                             (mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal31.value && ~mci_reg_hwif_out.internal_agg_error_non_fatal_mask.mask_agg_error_non_fatal31.value)
                                             ;

// Interrupt output is set, for any enabled conditions, when a new write
// sets FW_ERROR_FATAL or when a HW condition occurs that sets a bit
// in HW_ERROR_FATAL or when an aggregated fatal error occures in
// AGG_ERROR_FATAL
// Interrupt only deasserts on reset
always_ff@(posedge clk or negedge mci_rst_b) begin
    if(~mci_rst_b) begin
        mci_error_fatal <= 1'b0;
    end
    // FW write that SETS a new (non-masked) bit results in interrupt assertion
    else if (cif_resp_if.dv &&
             mci_reg_hwif_out.FW_ERROR_FATAL.error_code.swmod &&
             |(cif_resp_if.req_data.wdata & ~mci_reg_hwif_out.internal_fw_error_fatal_mask.mask.value & ~mci_reg_hwif_out.FW_ERROR_FATAL.error_code.value)) begin
        mci_error_fatal <= 1'b1;
    end
    // HW event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_hw_error_fatal_write) begin
        mci_error_fatal <= 1'b1;
    end
    // AGG event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_agg_error_fatal_write) begin
        mci_error_fatal <= 1'b1;
    end
    // NOTE: There is no mechanism to clear interrupt assertion by design.
    //       Platform MUST perform mci_rst_b in order to clear error_fatal
    //       output signal, per the integration spec.
    else begin
        mci_error_fatal <= mci_error_fatal;
    end
end
always_ff@(posedge clk or negedge mci_rst_b) begin
    if(~mci_rst_b) begin
        mci_error_non_fatal <= 1'b0;
    end
    // FW write that SETS a new (non-masked) bit results in interrupt assertion
    else if (cif_resp_if.dv &&
             mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.swmod &&
             |(cif_resp_if.req_data.wdata & ~mci_reg_hwif_out.internal_fw_error_non_fatal_mask.mask.value  & ~mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.value)) begin
        mci_error_non_fatal <= 1'b1;
    end
    // HW event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_hw_error_non_fatal_write) begin
        mci_error_non_fatal <= 1'b1;
    end
    // AGG event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_agg_error_non_fatal_write) begin
        mci_error_non_fatal <= 1'b1;
    end
    // If FW performs a write that clears all outstanding (unmasked) ERROR_NON_FATAL events, deassert interrupt
    else if (~unmasked_hw_error_non_fatal_is_set && ~unmasked_agg_error_non_fatal_is_set && 
             ~|(~mci_reg_hwif_out.internal_fw_error_non_fatal_mask.mask.value & mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.value)) begin
        mci_error_non_fatal <= 1'b0;
    end
    else begin
        mci_error_non_fatal <= mci_error_non_fatal;
    end
end

//TIE-OFFS
always_comb begin
    mci_reg_hwif_in.FW_ERROR_FATAL.error_code.we = 'b0;
    mci_reg_hwif_in.FW_ERROR_FATAL.error_code.next = 'h0;
    mci_reg_hwif_in.FW_ERROR_NON_FATAL.error_code.we = 'b0;
    mci_reg_hwif_in.FW_ERROR_NON_FATAL.error_code.next = 'h0;
end

////////////////////////////////////////////////////////
// AGG MCI Interrupts
////////////////////////////////////////////////////////
// FIXME should these be pluses
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal0_sts.hwset  = agg_error_fatal_sync[0];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal1_sts.hwset  = agg_error_fatal_sync[1];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal2_sts.hwset  = agg_error_fatal_sync[2];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal3_sts.hwset  = agg_error_fatal_sync[3];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal4_sts.hwset  = agg_error_fatal_sync[4];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal5_sts.hwset  = agg_error_fatal_sync[5];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal6_sts.hwset  = agg_error_fatal_sync[6];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal7_sts.hwset  = agg_error_fatal_sync[7];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal8_sts.hwset  = agg_error_fatal_sync[8];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal9_sts.hwset  = agg_error_fatal_sync[9];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal10_sts.hwset  = agg_error_fatal_sync[10];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal11_sts.hwset  = agg_error_fatal_sync[11];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal12_sts.hwset  = agg_error_fatal_sync[12];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal13_sts.hwset  = agg_error_fatal_sync[13];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal14_sts.hwset  = agg_error_fatal_sync[14];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal15_sts.hwset  = agg_error_fatal_sync[15];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal16_sts.hwset  = agg_error_fatal_sync[16];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal17_sts.hwset  = agg_error_fatal_sync[17];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal18_sts.hwset  = agg_error_fatal_sync[18];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal19_sts.hwset  = agg_error_fatal_sync[19];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal20_sts.hwset  = agg_error_fatal_sync[20];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal21_sts.hwset  = agg_error_fatal_sync[21];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal22_sts.hwset  = agg_error_fatal_sync[22];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal23_sts.hwset  = agg_error_fatal_sync[23];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal24_sts.hwset  = agg_error_fatal_sync[24];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal25_sts.hwset  = agg_error_fatal_sync[25];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal26_sts.hwset  = agg_error_fatal_sync[26];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal27_sts.hwset  = agg_error_fatal_sync[27];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal28_sts.hwset  = agg_error_fatal_sync[28];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal29_sts.hwset  = agg_error_fatal_sync[29];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal30_sts.hwset  = agg_error_fatal_sync[30];
always_comb mci_reg_hwif_in.intr_block_rf.error1_internal_intr_r.error_agg_error_fatal31_sts.hwset  = agg_error_fatal_sync[31];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal0_sts.hwset  = agg_error_non_fatal_sync[0];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal1_sts.hwset  = agg_error_non_fatal_sync[1];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal2_sts.hwset  = agg_error_non_fatal_sync[2];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal3_sts.hwset  = agg_error_non_fatal_sync[3];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal4_sts.hwset  = agg_error_non_fatal_sync[4];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal5_sts.hwset  = agg_error_non_fatal_sync[5];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal6_sts.hwset  = agg_error_non_fatal_sync[6];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal7_sts.hwset  = agg_error_non_fatal_sync[7];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal8_sts.hwset  = agg_error_non_fatal_sync[8];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal9_sts.hwset  = agg_error_non_fatal_sync[9];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal10_sts.hwset  = agg_error_non_fatal_sync[10];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal11_sts.hwset  = agg_error_non_fatal_sync[11];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal12_sts.hwset  = agg_error_non_fatal_sync[12];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal13_sts.hwset  = agg_error_non_fatal_sync[13];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal14_sts.hwset  = agg_error_non_fatal_sync[14];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal15_sts.hwset  = agg_error_non_fatal_sync[15];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal16_sts.hwset  = agg_error_non_fatal_sync[16];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal17_sts.hwset  = agg_error_non_fatal_sync[17];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal18_sts.hwset  = agg_error_non_fatal_sync[18];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal19_sts.hwset  = agg_error_non_fatal_sync[19];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal20_sts.hwset  = agg_error_non_fatal_sync[20];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal21_sts.hwset  = agg_error_non_fatal_sync[21];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal22_sts.hwset  = agg_error_non_fatal_sync[22];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal23_sts.hwset  = agg_error_non_fatal_sync[23];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal24_sts.hwset  = agg_error_non_fatal_sync[24];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal25_sts.hwset  = agg_error_non_fatal_sync[25];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal26_sts.hwset  = agg_error_non_fatal_sync[26];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal27_sts.hwset  = agg_error_non_fatal_sync[27];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal28_sts.hwset  = agg_error_non_fatal_sync[28];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal29_sts.hwset  = agg_error_non_fatal_sync[29];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal30_sts.hwset  = agg_error_non_fatal_sync[30];
always_comb mci_reg_hwif_in.intr_block_rf.notif1_internal_intr_r.notif_agg_error_non_fatal31_sts.hwset  = agg_error_non_fatal_sync[31];
////////////////////////////////////////////////////////
// WDT
////////////////////////////////////////////////////////
 
//  Looking for negedge on the wdt_timer*-timeout_sts register
//  meaning the interrupt has been serviced by SW. We then 
//  propagate this to the WDT to clear it's status
always_ff @(posedge clk or negedge mci_rst_b) begin
    if(!mci_rst_b) begin
        error_wdt_timer1_timeout_sts_prev <= 1'b0;
        error_wdt_timer2_timeout_sts_prev <= 1'b0;
    end
    else begin
        error_wdt_timer1_timeout_sts_prev <= mci_reg_hwif_out.intr_block_rf.error0_internal_intr_r.error_wdt_timer1_timeout_sts.value;
        error_wdt_timer2_timeout_sts_prev <= mci_reg_hwif_out.intr_block_rf.error0_internal_intr_r.error_wdt_timer2_timeout_sts.value;
    end
end

assign wdt_timer1_timeout_serviced = error_wdt_timer1_timeout_sts_prev & ~mci_reg_hwif_out.intr_block_rf.error0_internal_intr_r.error_wdt_timer1_timeout_sts.value;
assign wdt_timer2_timeout_serviced = error_wdt_timer2_timeout_sts_prev & ~mci_reg_hwif_out.intr_block_rf.error0_internal_intr_r.error_wdt_timer2_timeout_sts.value;;


// WDT timeout Interrupts
assign mci_reg_hwif_in.intr_block_rf.error0_internal_intr_r.error_wdt_timer1_timeout_sts.hwset = t1_timeout_p;
assign mci_reg_hwif_in.intr_block_rf.error0_internal_intr_r.error_wdt_timer2_timeout_sts.hwset = t2_timeout_p;

//Set WDT status reg
always_comb begin
    mci_reg_hwif_in.WDT_STATUS.t1_timeout.next = t1_timeout;
    mci_reg_hwif_in.WDT_STATUS.t2_timeout.next = t2_timeout;
end


// MCU SRAM Interrupts
assign mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mcu_sram_ecc_cor_sts.hwset = mcu_sram_single_ecc_error;

///////////////////////////////////////////////
// MCI REG Module      
///////////////////////////////////////////////
mci_reg i_mci_reg (

        .clk  (clk),
        .rst  ('0), // FIXME why is this tied off in soc_ifc?

        .s_cpuif_req            (cif_resp_if.dv),
        .s_cpuif_req_is_wr      (cif_resp_if.req_data.write),
        .s_cpuif_addr           (cif_resp_if.req_data.addr[MCI_REG_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data        (cif_resp_if.req_data.wdata),
        .s_cpuif_wr_biten       (c_cpuif_wr_biten),
        .s_cpuif_req_stall_wr   (),     // FIXME why isn't this used?
        .s_cpuif_req_stall_rd   (),   // FIXME why isn't this connected?
        .s_cpuif_rd_ack         (),     // FIXME why isn't this used?
        .s_cpuif_rd_err         (mci_reg_read_error),
        .s_cpuif_rd_data        (cif_resp_if.rdata),   // FIXME should this be masked for security?
        .s_cpuif_wr_ack         (),     // FIXME why isn't this used?
        .s_cpuif_wr_err         (mci_reg_write_error),

        .hwif_in                (mci_reg_hwif_in),
        .hwif_out               (mci_reg_hwif_out)

);


endmodule
