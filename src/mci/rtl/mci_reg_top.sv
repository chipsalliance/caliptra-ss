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


module mci_reg_top 
    import mci_reg_pkg::*;
    import mci_pkg::*;
    import mci_mcu_trace_buffer_pkg::*;
    import mci_dmi_pkg::*;
    import soc_ifc_pkg::*;
    #(
        parameter AXI_USER_WIDTH = 32
    
        //Mailbox configuration
        ,parameter MCU_MBOX0_SIZE_KB = 128
        ,parameter [4:0] SET_MCU_MBOX0_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
        ,parameter [4:0][31:0] MCU_MBOX0_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}
        ,parameter MCU_MBOX1_SIZE_KB = 4
        ,parameter [4:0] SET_MCU_MBOX1_AXI_USER_INTEG   = { 1'b0,          1'b0,          1'b0,          1'b0,          1'b0}
        ,parameter [4:0][31:0] MCU_MBOX1_VALID_AXI_USER = {32'h4444_4444, 32'h3333_3333, 32'h2222_2222, 32'h1111_1111, 32'h0000_0000}
        
        ,parameter MCU_SRAM_SIZE_KB = 512 
        ,parameter MIN_MCU_RST_COUNTER_WIDTH = 4 

    )
    (
    input logic clk,

    // Resets
    input logic mci_rst_b,
    input logic mcu_rst_b,
    input logic cptra_rst_b,
    input logic mci_pwrgood,

    // DFT
    input logic scan_mode,

    // REG HWIF signals
    output mci_reg__out_t mci_reg_hwif_out,

    // AXI Privileged requests
    input logic axi_mci_soc_config_req,
    input logic axi_mcu_sram_config_req,
    input logic axi_mcu_req,

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

    
    // DMI
    output logic        mcu_dmi_core_enable,
    output logic        mcu_dmi_uncore_enable,
    input  logic        mcu_dmi_uncore_en,
    input  logic        mcu_dmi_uncore_wr_en,
    input  logic [ 6:0] mcu_dmi_uncore_addr,
    input  logic [31:0] mcu_dmi_uncore_wdata,
    output logic [31:0] mcu_dmi_uncore_rdata,

    // Trace buffer
    output logic         mcu_trace_buffer_dmi_reg_wen,
    output logic [31:0]  mcu_trace_buffer_dmi_reg_wdata,
    output logic [6:0]   mcu_trace_buffer_dmi_reg_addr,
    input mci_mcu_trace_buffer_dmi_reg_t mcu_trace_buffer_dmi_reg,

    // MBOX
    // unused in 2.0 input  mbox_dmi_reg_t mbox0_dmi_reg,
    // unused in 2.0 input  mbox_dmi_reg_t mbox1_dmi_reg,
    // unused in 2.0 output logic dmi_mbox0_inc_rdptr,
    // unused in 2.0 output logic dmi_mbox0_inc_wrptr,
    // unused in 2.0 output logic dmi_mbox1_inc_rdptr,
    // unused in 2.0 output logic dmi_mbox1_inc_wrptr,
    // unused in 2.0 output logic dmi_mbox0_wen,
    // unused in 2.0 output logic dmi_mbox1_wen,
    input  logic mcu_mbox0_data_avail,
    input  logic mcu_mbox1_data_avail,
    input  logic cptra_mbox_data_avail,
    input  logic mcu_mbox0_target_user_done,
    input  logic mcu_mbox1_target_user_done,
    output logic [4:0][AXI_USER_WIDTH-1:0] valid_mbox0_users,
    output logic [4:0][AXI_USER_WIDTH-1:0] valid_mbox1_users,
    input  logic soc_req_mbox0_lock,
    input  logic soc_req_mbox1_lock,
    input  logic mbox0_sram_single_ecc_error,
    input  logic mbox0_sram_double_ecc_error,
    input  logic mbox1_sram_single_ecc_error,
    input  logic mbox1_sram_double_ecc_error,

    // LCC Gasket
    input soc_ifc_pkg::security_state_t                security_state_o,

    // SOC Interrupts
    output logic all_error_fatal,
    output logic all_error_non_fatal,

    // MCU interrupts
    output logic mcu_timer_int,
    output logic mci_intr,

    // Debug Intent
    input logic ss_debug_intent,
    output logic mci_ss_debug_intent,

    // AXI Straps
    input logic [AXI_USER_WIDTH-1:0] strap_mcu_lsu_axi_user,
    input logic [AXI_USER_WIDTH-1:0] strap_mcu_ifu_axi_user,
    input logic [AXI_USER_WIDTH-1:0] strap_mcu_sram_config_axi_user,
    input logic [AXI_USER_WIDTH-1:0] strap_mci_soc_config_axi_user,


    // MCU Reset vector
    input  logic [31:0] strap_mcu_reset_vector, // default reset vector
    output logic [31:0] mcu_reset_vector,       // reset vector used by MCU

    // OTP
    input logic intr_otp_operation_done,

    // NMI
    input  logic nmi_intr,
    output logic [31:0] mcu_nmi_vector,

    // MISC 
    input  logic mcu_sram_fw_exec_region_lock,
    output logic mcu_sram_fw_exec_region_lock_dmi_override,

    // MCU SRAM specific signals
    input  logic        mcu_sram_single_ecc_error,
    input  logic        mcu_sram_double_ecc_error,
    input  logic        mcu_sram_dmi_axi_collision_error,
    output logic        mcu_sram_dmi_uncore_en,
    output logic        mcu_sram_dmi_uncore_wr_en,
    output logic [ 6:0] mcu_sram_dmi_uncore_addr,
    output logic [31:0] mcu_sram_dmi_uncore_wdata,
    input  logic [31:0] mcu_sram_dmi_uncore_rdata,

    // Boot status
    input  logic mcu_reset_once,
    input  mci_boot_fsm_state_e boot_fsm, 

    
    // Caliptra internal fabric response interface
    cif_if.response  cif_resp_if

    );

// Reset reason
logic pwrgood_toggle_hint;
logic Warm_Reset_Capture_Flag;

// Interrupts 
logic mci_error_intr;
logic mci_notif_intr;
    
// Security
logic security_state_debug_locked_d;
logic security_state_debug_locked_edge;
logic scan_mode_f;
logic scan_mode_p;

// DMI
logic mcu_dmi_uncore_dbg_unlocked_en;
logic mcu_dmi_uncore_locked_en;
logic mcu_dmi_uncore_dbg_unlocked_wr_en;
logic mcu_dmi_uncore_locked_wr_en  ;
// unused in 2.0 logic mcu_dmi_uncore_mbox0_dout_access_f;
// unused in 2.0 logic mcu_dmi_uncore_mbox0_din_access_f;
// unused in 2.0 logic mcu_dmi_uncore_mbox1_dout_access_f;
// unused in 2.0 logic mcu_dmi_uncore_mbox1_din_access_f;
MCI_DMI_MCI_HW_OVERRIDE_REG_t MCI_DMI_MCI_HW_OVERRIDE_REG;

logic [31:0] mcu_dmi_uncore_dbg_unlocked_rdata_in;
logic [31:0] mcu_dmi_uncore_locked_rdata_in;

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

// Misc
logic [1:0] generic_input_toggle;
logic axi_mcu_or_debug_req;
logic axi_cptra_or_debug_req;

// MBOX
logic mcu_mbox0_data_avail_d;
logic mcu_mbox0_cmd_avail_p;
logic mcu_mbox1_data_avail_d;
logic mcu_mbox1_cmd_avail_p;
logic cptra_mbox_data_avail_d;
logic cptra_mbox_cmd_avail_p;
logic mcu_mbox0_target_user_done_d;
logic mcu_mbox0_target_user_done_p;
logic mcu_mbox1_target_user_done_d;
logic mcu_mbox1_target_user_done_p;

logic strap_we_sticky;
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
) u_prim_flop_2sync_mic_generic_wire_in (
  .clk_i(clk),
  .rst_ni(mci_rst_b),
  .d_i(mci_generic_input_wires),
  .q_o({mci_reg_hwif_in.GENERIC_INPUT_WIRES[1].wires.next, mci_reg_hwif_in.GENERIC_INPUT_WIRES[0].wires.next}));

assign mci_generic_output_wires = {mci_reg_hwif_out.GENERIC_OUTPUT_WIRES[1].wires.value, mci_reg_hwif_out.GENERIC_OUTPUT_WIRES[0].wires.value};

always_comb begin
    for (int i = 0; i < 2; i++) begin
        generic_input_toggle[i] = |(mci_reg_hwif_out.GENERIC_INPUT_WIRES[i].wires.value ^ mci_reg_hwif_in.GENERIC_INPUT_WIRES[i].wires.next);
    end
end

assign  mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_gen_in_toggle_sts.hwset  = |generic_input_toggle;

assign  mci_reg_hwif_in.intr_block_rf.error0_internal_intr_r.error_internal_sts.hwset  = '0; // TODO

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
// STRAPS / TAP ACCESS 
///////////////////////////////////////////////

// Subsystem straps capture the initial value on mci_rst_b deassertion.
always_ff @(posedge clk or negedge mci_rst_b) begin
     if(~mci_rst_b) begin
        strap_we <= 1'b1;
    end
    else begin
        strap_we <= 1'b0;
    end
end

assign strap_we_sticky = strap_we & ~mci_reg_hwif_out.SS_CONFIG_DONE_STICKY.done.value;

// Value
always_comb begin
    // STRAP with TAP ACCESS
    mci_reg_hwif_in.SS_DEBUG_INTENT.debug_intent.next   = strap_we_sticky ? ss_debug_intent : mcu_dmi_uncore_wdata[0];
    mci_reg_hwif_in.MCU_RESET_VECTOR.vec.next           = strap_we ? strap_mcu_reset_vector : mcu_dmi_uncore_wdata ; 

    // REGISTERS WITH TAP ACCESS
    mci_reg_hwif_in.RESET_REQUEST.mcu_req.next          = mcu_dmi_uncore_wdata[0] ; 
    mci_reg_hwif_in.MCI_BOOTFSM_GO.go.next              = mcu_dmi_uncore_wdata[0] ; 
    mci_reg_hwif_in.CPTRA_BOOT_GO.go.next               = mcu_dmi_uncore_wdata[0] ; 
    mci_reg_hwif_in.SS_CONFIG_DONE.done.next            = mcu_dmi_uncore_wdata[0] ; 
    mci_reg_hwif_in.SS_CONFIG_DONE_STICKY.done.next     = mcu_dmi_uncore_wdata[0] ; 
    mci_reg_hwif_in.FW_SRAM_EXEC_REGION_SIZE.size.next  = mcu_dmi_uncore_wdata[15:0] ; 
    mci_reg_hwif_in.MCU_NMI_VECTOR.vec.next             = mcu_dmi_uncore_wdata ; 

    // Straps with no override
    mci_reg_hwif_in.MCU_IFU_AXI_USER.value.next = { {(32-$bits(strap_mcu_ifu_axi_user)){1'b0}}, strap_mcu_ifu_axi_user};
    mci_reg_hwif_in.MCU_LSU_AXI_USER.value.next = { {(32-$bits(strap_mcu_lsu_axi_user)){1'b0}}, strap_mcu_lsu_axi_user};
    mci_reg_hwif_in.MCU_SRAM_CONFIG_AXI_USER.value.next = { {(32-$bits(strap_mcu_sram_config_axi_user)){1'b0}}, strap_mcu_sram_config_axi_user} ;
    mci_reg_hwif_in.MCI_SOC_CONFIG_AXI_USER.value.next  = { {(32-$bits(strap_mci_soc_config_axi_user )){1'b0}}, strap_mci_soc_config_axi_user} ;

end

// Write enable
always_comb begin
    // STRAPS with TAP ACCESS
    mci_reg_hwif_in.SS_DEBUG_INTENT.debug_intent.we     = strap_we_sticky | (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_SS_DEBUG_INTENT));
    mci_reg_hwif_in.MCU_RESET_VECTOR.vec.we             = strap_we | (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_MCU_RESET_VECTOR));
    
    // REGISTERS WITH TAP ACCESS
    mci_reg_hwif_in.RESET_REQUEST.mcu_req.we            =  (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_RESET_REQUEST));
    mci_reg_hwif_in.MCI_BOOTFSM_GO.go.we                =  (mcu_dmi_uncore_locked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_MCI_BOOTFSM_GO));
    mci_reg_hwif_in.CPTRA_BOOT_GO.go.we                 =  (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_CPTRA_BOOT_GO));
    mci_reg_hwif_in.SS_CONFIG_DONE.done.we              =  (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_SS_CONFIG_DONE));
    mci_reg_hwif_in.SS_CONFIG_DONE_STICKY.done.we       =  (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_SS_CONFIG_DONE_STICKY));
    mci_reg_hwif_in.FW_SRAM_EXEC_REGION_SIZE.size.we    =  (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_FW_SRAM_EXEC_REGION_SIZE));
    mci_reg_hwif_in.MCU_NMI_VECTOR.vec.we               =  (mcu_dmi_uncore_dbg_unlocked_wr_en & 
                                                            (mcu_dmi_uncore_addr == MCI_DMI_MCU_NMI_VECTOR));
end

always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        MCI_DMI_MCI_HW_OVERRIDE_REG <= '0;
    end
    else begin
        if(mcu_dmi_uncore_dbg_unlocked_wr_en & 
            (mcu_dmi_uncore_addr == MCI_DMI_MCI_HW_OVERRIDE)) begin
            MCI_DMI_MCI_HW_OVERRIDE_REG <= mcu_dmi_uncore_wdata;
        end
    end
end

assign mcu_sram_fw_exec_region_lock_dmi_override = MCI_DMI_MCI_HW_OVERRIDE_REG.mcu_sram_fw_exec_region_lock;


assign mci_ss_debug_intent  = mci_reg_hwif_out.SS_DEBUG_INTENT.debug_intent.value;
assign mcu_reset_vector     = mci_reg_hwif_out.MCU_RESET_VECTOR.vec.value;

assign mci_reg_hwif_in.HW_CONFIG0.MCU_MBOX0_SRAM_SIZE.next = MCU_MBOX0_SIZE_KB;
assign mci_reg_hwif_in.HW_CONFIG0.MCU_MBOX1_SRAM_SIZE.next = MCU_MBOX1_SIZE_KB;
assign mci_reg_hwif_in.HW_CONFIG1.MCU_SRAM_SIZE.next = MCU_SRAM_SIZE_KB;
assign mci_reg_hwif_in.HW_CONFIG1.MIN_MCU_RST_COUNTER_WIDTH.next = MIN_MCU_RST_COUNTER_WIDTH;

///////////////////////////////////////////////
// Security Related      
///////////////////////////////////////////////
assign mci_reg_hwif_in.SECURITY_STATE.device_lifecycle.next = security_state_o.device_lifecycle;
assign mci_reg_hwif_in.SECURITY_STATE.debug_locked.next     = security_state_o.debug_locked;
assign mci_reg_hwif_in.SECURITY_STATE.scan_mode.next        = scan_mode;


// Generate a pulse to set the interrupt bit
always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        security_state_debug_locked_d <= '0;
    end
    else begin
        security_state_debug_locked_d <= security_state_o.debug_locked;
    end
end

always_comb security_state_debug_locked_edge = security_state_o.debug_locked ^ security_state_debug_locked_d;

// Generate a pulse to set the interrupt bit
always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        scan_mode_f <= '0;
    end
    else begin
        scan_mode_f <= scan_mode;
    end
end

always_comb scan_mode_p = scan_mode & ~scan_mode_f;

assign mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_scan_mode_sts.hwset = scan_mode_p;
assign mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_debug_locked_sts.hwset = security_state_debug_locked_edge;




///////////////////////////////////////////////
// DMI                   
///////////////////////////////////////////////

assign mcu_dmi_core_enable          = !security_state_o.debug_locked;
assign mcu_dmi_uncore_enable        = (!security_state_o.debug_locked) || (security_state_o.device_lifecycle == DEVICE_MANUFACTURING) || mci_ss_debug_intent;

//Uncore registers open for all cases
always_comb mcu_dmi_uncore_locked_en = mcu_dmi_uncore_en;

//Uncore registers only open for debug unlock 
always_comb mcu_dmi_uncore_dbg_unlocked_en = mcu_dmi_uncore_en & 
                                                (~(security_state_o.debug_locked)  
                                                 );



always_comb mcu_dmi_uncore_dbg_unlocked_wr_en   = (mcu_dmi_uncore_wr_en & mcu_dmi_uncore_dbg_unlocked_en);
always_comb mcu_dmi_uncore_locked_wr_en         = (mcu_dmi_uncore_wr_en & mcu_dmi_uncore_locked_en);

//DMI unlocked register read mux
// NOTE - must contain a super set of the uncore_locked_rdata_in
always_comb mcu_dmi_uncore_dbg_unlocked_rdata_in =  ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_SRAM_ADDR              )}}   &  mcu_sram_dmi_uncore_rdata                        )  | 
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_SRAM_DATA              )}}   &  mcu_sram_dmi_uncore_rdata                        )  | 
                                                    // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_DLEN             )}}   &  mbox0_dmi_reg.MBOX_DLEN                     )  | 
                                                    // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_DOUT             )}}   &  mbox0_dmi_reg.MBOX_DOUT                     )  | 
                                                    // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_STATUS           )}}   &  mbox0_dmi_reg.MBOX_STATUS                   )  |
                                                    // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_DLEN             )}}   &  mbox1_dmi_reg.MBOX_DLEN                     )  | 
                                                    // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_DOUT             )}}   &  mbox1_dmi_reg.MBOX_DOUT                     )  | 
                                                    // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_STATUS           )}}   &  mbox1_dmi_reg.MBOX_STATUS                   )  | 
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_TRACE_STATUS           )}}   &  32'(mcu_trace_buffer_dmi_reg.TRACE_STATUS)            )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_TRACE_CONFIG           )}}   &  32'(mcu_trace_buffer_dmi_reg.TRACE_CONFIG)            )  | 
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_TRACE_WR_PTR           )}}   &  32'(mcu_trace_buffer_dmi_reg.TRACE_WR_PTR)            )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_TRACE_RD_PTR           )}}   &  32'(mcu_trace_buffer_dmi_reg.TRACE_RD_PTR)            )  | 
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_TRACE_DATA             )}}   &  32'(mcu_trace_buffer_dmi_reg.TRACE_DATA)              )  | 
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_FLOW_STATUS             )}}   &  32'({mci_reg_hwif_out.HW_FLOW_STATUS.boot_fsm.value}))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_RESET_REASON               )}}   &  32'({mci_reg_hwif_out.RESET_REASON.WARM_RESET.value,
                                                                                                                                  mci_reg_hwif_out.RESET_REASON.FW_BOOT_UPD_RESET.value,
                                                                                                                                  mci_reg_hwif_out.RESET_REASON.FW_HITLESS_UPD_RESET.value})  )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_RESET_STATUS               )}}   &  32'({mci_reg_hwif_out.RESET_STATUS.mcu_reset_sts.value,
                                                                                                                                  mci_reg_hwif_out.RESET_STATUS.cptra_reset_sts.value}))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_FLOW_STATUS             )}}   &  32'(mci_reg_hwif_out.FW_FLOW_STATUS.status.value)     )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_ERROR_FATAL             )}}   &  32'({mci_reg_hwif_out.HW_ERROR_FATAL.mcu_sram_dmi_axi_collision.value,
                                                                                                                                  mci_reg_hwif_out.HW_ERROR_FATAL.nmi_pin.value,
                                                                                                                                  mci_reg_hwif_out.HW_ERROR_FATAL.mcu_sram_ecc_unc.value}))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_AGG_ERROR_FATAL            )}}   &  `SS_DMI_AGG_ERR_CONCAT(mci_reg_hwif_out.AGG_ERROR_FATAL.agg_error_fatal))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_ERROR_NON_FATAL         )}}   &  32'({mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox1_ecc_unc.value,
                                                                                                                                  mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox0_ecc_unc.value}) )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_AGG_ERROR_NON_FATAL        )}}   &  `SS_DMI_AGG_ERR_CONCAT(mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_ERROR_FATAL             )}}   &  32'(mci_reg_hwif_out.FW_ERROR_FATAL.error_code.value) )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_ERROR_NON_FATAL         )}}   &  32'(mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_ERROR_ENC               )}}   &  32'(mci_reg_hwif_out.HW_ERROR_ENC.error_code.value)   )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_ERROR_ENC               )}}   &  32'(mci_reg_hwif_out.FW_ERROR_ENC.error_code.value)   )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_0   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[0].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_1   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[1].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_2   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[2].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_3   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[3].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_4   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[4].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_5   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[5].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_6   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[6].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_7   )}}   &  32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[7].error_info.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_RESET_REQUEST              )}}   &  32'(mci_reg_hwif_out.RESET_REQUEST.mcu_req.value)        )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCI_BOOTFSM_GO             )}}   &  32'(mci_reg_hwif_out.MCI_BOOTFSM_GO.go.value)            )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_CPTRA_BOOT_GO              )}}   &  32'(mci_reg_hwif_out.CPTRA_BOOT_GO.go.value)             )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_SRAM_EXEC_REGION_SIZE   )}}   &  32'(mci_reg_hwif_out.FW_SRAM_EXEC_REGION_SIZE.size.value))  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_RESET_VECTOR           )}}   &  32'(mci_reg_hwif_out.MCU_RESET_VECTOR.vec.value)         )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_SS_DEBUG_INTENT            )}}   &  32'(mci_reg_hwif_out.SS_DEBUG_INTENT.debug_intent.value) )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_SS_CONFIG_DONE             )}}   &  32'(mci_reg_hwif_out.SS_CONFIG_DONE.done.value)          )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_SS_CONFIG_DONE_STICKY      )}}   &  32'(mci_reg_hwif_out.SS_CONFIG_DONE_STICKY.done.value)   )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCU_NMI_VECTOR             )}}   &  32'(mci_reg_hwif_out.MCU_NMI_VECTOR.vec.value)           )  |
                                                    ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCI_HW_OVERRIDE            )}}   &  32'(MCI_DMI_MCI_HW_OVERRIDE_REG)                             )  ;


// Registers accessable while in a locked state
always_comb mcu_dmi_uncore_locked_rdata_in =  // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_DLEN             )}}   &  mbox0_dmi_reg.MBOX_DLEN                     )  | 
                                              // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_DOUT             )}}   &  mbox0_dmi_reg.MBOX_DOUT                     )  | 
                                              // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_STATUS           )}}   &  mbox0_dmi_reg.MBOX_STATUS                   )  |
                                              // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_DLEN             )}}   &  mbox1_dmi_reg.MBOX_DLEN                     )  | 
                                              // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_DOUT             )}}   &  mbox1_dmi_reg.MBOX_DOUT                     )  | 
                                              // unused in 2.0 ({32{(mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_STATUS           )}}   &  mbox1_dmi_reg.MBOX_STATUS                   )  | 
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_MCI_BOOTFSM_GO             )}}   & 32'(mci_reg_hwif_out.MCI_BOOTFSM_GO.go.value) )  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_FLOW_STATUS             )}}   & 32'(mci_reg_hwif_out.HW_FLOW_STATUS.boot_fsm.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_RESET_REASON               )}}   & 32'({mci_reg_hwif_out.RESET_REASON.WARM_RESET.value,
                                                                                                                           mci_reg_hwif_out.RESET_REASON.FW_BOOT_UPD_RESET.value,
                                                                                                                           mci_reg_hwif_out.RESET_REASON.FW_HITLESS_UPD_RESET.value}) )  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_RESET_STATUS               )}}   & 32'({mci_reg_hwif_out.RESET_STATUS.mcu_reset_sts.value,
                                                                                                                           mci_reg_hwif_out.RESET_STATUS.cptra_reset_sts.value}))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_FLOW_STATUS             )}}   & 32'(mci_reg_hwif_out.FW_FLOW_STATUS.status.value         ))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_ERROR_FATAL             )}}   & 32'({mci_reg_hwif_out.HW_ERROR_FATAL.mcu_sram_dmi_axi_collision.value,
                                                                                                                           mci_reg_hwif_out.HW_ERROR_FATAL.nmi_pin.value,
                                                                                                                           mci_reg_hwif_out.HW_ERROR_FATAL.mcu_sram_ecc_unc.value}))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_AGG_ERROR_FATAL            )}}   & `SS_DMI_AGG_ERR_CONCAT(mci_reg_hwif_out.AGG_ERROR_FATAL.agg_error_fatal))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_ERROR_NON_FATAL         )}}   & 32'({mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox1_ecc_unc.value,
                                                                                                                           mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox0_ecc_unc.value}) )  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_AGG_ERROR_NON_FATAL        )}}   & `SS_DMI_AGG_ERR_CONCAT(mci_reg_hwif_out.AGG_ERROR_NON_FATAL.agg_error_non_fatal))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_ERROR_FATAL             )}}   & 32'(mci_reg_hwif_out.FW_ERROR_FATAL.error_code.value) )  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_ERROR_NON_FATAL         )}}   & 32'(mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_HW_ERROR_ENC               )}}   & 32'(mci_reg_hwif_out.HW_ERROR_ENC.error_code.value)   )  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_ERROR_ENC               )}}   & 32'(mci_reg_hwif_out.FW_ERROR_ENC.error_code.value)   )  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_0   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[0].error_info.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_1   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[1].error_info.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_2   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[2].error_info.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_3   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[3].error_info.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_4   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[4].error_info.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_5   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[5].error_info.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_6   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[6].error_info.value))  |
                                              ({32{(mcu_dmi_uncore_addr == MCI_DMI_FW_EXTENDED_ERROR_INFO_7   )}}   & 32'(mci_reg_hwif_out.FW_EXTENDED_ERROR_INFO[7].error_info.value));  
                                           
// unused in 2.0 always_comb dmi_mbox0_inc_rdptr = mcu_dmi_uncore_mbox0_dout_access_f & ~mcu_dmi_uncore_locked_en;
// unused in 2.0 always_comb dmi_mbox0_inc_wrptr = mcu_dmi_uncore_mbox0_din_access_f &  ~mcu_dmi_uncore_locked_en;
// unused in 2.0 always_comb dmi_mbox1_inc_rdptr = mcu_dmi_uncore_mbox1_dout_access_f & ~mcu_dmi_uncore_locked_en;
// unused in 2.0 always_comb dmi_mbox1_inc_wrptr = mcu_dmi_uncore_mbox1_din_access_f &  ~mcu_dmi_uncore_locked_en;
// unused in 2.0 always_comb dmi_mbox0_wen = mcu_dmi_uncore_locked_en & mcu_dmi_uncore_wr_en;
// unused in 2.0 always_comb dmi_mbox1_wen = mcu_dmi_uncore_locked_en & mcu_dmi_uncore_wr_en;

// MCU Trace buffer DMI
always_comb mcu_trace_buffer_dmi_reg_wen = mcu_dmi_uncore_dbg_unlocked_en & mcu_dmi_uncore_wr_en;
always_comb mcu_trace_buffer_dmi_reg_wdata = mcu_dmi_uncore_wdata;
always_comb mcu_trace_buffer_dmi_reg_addr = mcu_dmi_uncore_addr;

// MCU SRAM DMI
always_comb mcu_sram_dmi_uncore_en = mcu_dmi_uncore_dbg_unlocked_en;
always_comb mcu_sram_dmi_uncore_wr_en = mcu_dmi_uncore_dbg_unlocked_wr_en;
always_comb mcu_sram_dmi_uncore_addr = mcu_dmi_uncore_addr;
always_comb mcu_sram_dmi_uncore_wdata = mcu_dmi_uncore_wdata;

always_comb mci_reg_hwif_in.intr_block_rf.error0_internal_intr_r.error_mcu_sram_dmi_axi_collision_sts.hwset           = mcu_sram_dmi_axi_collision_error; // Set by any protocol error violation (mirrors the bits in CPTRA_HW_ERROR_NON_FATAL)
                                              
always_ff @(posedge clk or negedge mci_pwrgood) begin
    if (~mci_pwrgood) begin
      mcu_dmi_uncore_rdata <= '0;
      // unused in 2.0 mcu_dmi_uncore_mbox0_dout_access_f <= '0;
      // unused in 2.0 mcu_dmi_uncore_mbox0_din_access_f  <= '0;
      // unused in 2.0 mcu_dmi_uncore_mbox1_dout_access_f <= '0;
      // unused in 2.0 mcu_dmi_uncore_mbox1_din_access_f  <= '0;
    end  
    else begin
        mcu_dmi_uncore_rdata <= mcu_dmi_uncore_dbg_unlocked_en ? mcu_dmi_uncore_dbg_unlocked_rdata_in : 
                                mcu_dmi_uncore_locked_en       ? mcu_dmi_uncore_locked_rdata_in : 
                                                                 mcu_dmi_uncore_rdata;

        // unused in 2.0 mcu_dmi_uncore_mbox0_dout_access_f <= mcu_dmi_uncore_locked_en & ~mcu_dmi_uncore_wr_en & (mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_DOUT);
        // unused in 2.0 mcu_dmi_uncore_mbox0_din_access_f  <= mcu_dmi_uncore_locked_en &  mcu_dmi_uncore_wr_en & (mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX0_DIN);
        // unused in 2.0 mcu_dmi_uncore_mbox1_dout_access_f <= mcu_dmi_uncore_locked_en & ~mcu_dmi_uncore_wr_en & (mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_DOUT);
        // unused in 2.0 mcu_dmi_uncore_mbox1_din_access_f  <= mcu_dmi_uncore_locked_en &  mcu_dmi_uncore_wr_en & (mcu_dmi_uncore_addr == MCI_DMI_REG_MBOX1_DIN);
  end  
end
                                            

// Resets
assign mci_reg_hwif_in.mci_rst_b = mci_rst_b;
assign mci_reg_hwif_in.mci_pwrgood = mci_pwrgood;

// Agent requests
assign mci_reg_hwif_in.axi_mcu_req              = axi_mcu_req;
assign mci_reg_hwif_in.ss_config_unlock         = ~mci_reg_hwif_out.SS_CONFIG_DONE.done.value;
assign mci_reg_hwif_in.ss_config_unlock_sticky  = ~mci_reg_hwif_out.SS_CONFIG_DONE_STICKY.done.value;
assign mci_reg_hwif_in.axi_mcu_or_mci_soc_config_req                            = (axi_mcu_req | axi_mci_soc_config_req);
assign mci_reg_hwif_in.axi_mcu_req_or_mci_soc_config_req__cap_unlock            = (axi_mcu_req | axi_mci_soc_config_req) & ~mci_reg_hwif_out.CAP_LOCK.lock.value;
assign mci_reg_hwif_in.axi_mcu_or_mci_soc_config_req__ss_config_unlock          = (axi_mcu_req | axi_mci_soc_config_req) & ~mci_reg_hwif_out.SS_CONFIG_DONE.done.value;
assign mci_reg_hwif_in.axi_mcu_or_mci_soc_config_req__ss_config_unlock_sticky   = (axi_mcu_req | axi_mci_soc_config_req) & ~mci_reg_hwif_out.SS_CONFIG_DONE_STICKY.done.value;
assign mci_reg_hwif_in.axi_mcu_or_mcu_sram_config_req                           = (axi_mcu_req | axi_mcu_sram_config_req);



///////////////////////////////////////////////
// MTIME                       
///////////////////////////////////////////////
// mtime always increments, but if it's being written by software the write
// value will update the register. Deasserting incr in this case prevents the
// SW write from being dropped (due to RDL compiler failing to give SW precedence properly).
assign mci_reg_hwif_in.MCU_RV_MTIME_L.count_l.incr = !(cif_resp_if.dv && mci_reg_hwif_out.MCU_RV_MTIME_L.count_l.swmod);
assign mci_reg_hwif_in.MCU_RV_MTIME_H.count_h.incr = !(cif_resp_if.dv && mci_reg_hwif_out.MCU_RV_MTIME_H.count_h.swmod) && mci_reg_hwif_out.MCU_RV_MTIME_L.count_l.overflow;
assign mcu_timer_int  =  {mci_reg_hwif_out.MCU_RV_MTIME_H.count_h.value     ,mci_reg_hwif_out.MCU_RV_MTIME_L.count_l.value}
                     >=
                     {mci_reg_hwif_out.MCU_RV_MTIMECMP_H.compare_h.value,mci_reg_hwif_out.MCU_RV_MTIMECMP_L.compare_l.value};
///////////////////////////////////////////////
// Filtering by AXI_USER       
///////////////////////////////////////////////


always_comb begin
    for (int i=0; i<5; i++) begin
        //once locked, can't be cleared until reset
        mci_reg_hwif_in.MBOX0_AXI_USER_LOCK[i].LOCK.swwel = mci_reg_hwif_out.MBOX0_AXI_USER_LOCK[i].LOCK.value;
        //lock the writes to valid user field once lock is set
        mci_reg_hwif_in.MBOX0_VALID_AXI_USER[i].AXI_USER.swwel = mci_reg_hwif_out.MBOX0_AXI_USER_LOCK[i].LOCK.value;
        //If integrator set AXI_USER values at integration time, pick it up from the define
        valid_mbox0_users[i] = SET_MCU_MBOX0_AXI_USER_INTEG[i] ? MCU_MBOX0_VALID_AXI_USER[i][AXI_USER_WIDTH-1:0] :
                               mci_reg_hwif_out.MBOX0_AXI_USER_LOCK[i].LOCK.value ?
                               mci_reg_hwif_out.MBOX0_VALID_AXI_USER[i].AXI_USER.value[AXI_USER_WIDTH-1:0] :
                               MCU_DEF_MBOX_VALID_AXI_USER;
    end
end


always_comb begin
    for (int i=0; i<5; i++) begin
        //once locked, can't be cleared until reset
        mci_reg_hwif_in.MBOX1_AXI_USER_LOCK[i].LOCK.swwel = mci_reg_hwif_out.MBOX1_AXI_USER_LOCK[i].LOCK.value;
        //lock the writes to valid user field once lock is set
        mci_reg_hwif_in.MBOX1_VALID_AXI_USER[i].AXI_USER.swwel = mci_reg_hwif_out.MBOX1_AXI_USER_LOCK[i].LOCK.value;
        //If integrator set AXI_USER values at integration time, pick it up from the define
        valid_mbox1_users[i] = SET_MCU_MBOX1_AXI_USER_INTEG[i] ? MCU_MBOX1_VALID_AXI_USER[i][AXI_USER_WIDTH-1:0] :
                               mci_reg_hwif_out.MBOX1_AXI_USER_LOCK[i].LOCK.value ?
                               mci_reg_hwif_out.MBOX1_VALID_AXI_USER[i].AXI_USER.value[AXI_USER_WIDTH-1:0] :
                               MCU_DEF_MBOX_VALID_AXI_USER;
    end
end

///////////////////////////////////////////////
// MCU Reset Request interrupt 
///////////////////////////////////////////////


always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mcu_sram_fw_exec_region_lock_prev <= 0;
    end
    else begin
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

assign mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_cptra_mcu_reset_req_sts.hwset = cptra_mcu_rst_req;

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
// Boot FSM Status
///////////////////////////////////////////////

assign mci_reg_hwif_in.RESET_STATUS.cptra_reset_sts.next = ~cptra_rst_b;
assign mci_reg_hwif_in.RESET_STATUS.mcu_reset_sts.next   = ~mcu_rst_b;

assign mci_reg_hwif_in.HW_FLOW_STATUS.boot_fsm.next = boot_fsm;


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
// only due to warm reset.
always_comb begin
    if (!Warm_Reset_Capture_Flag) begin
         mci_reg_hwif_in.RESET_REASON.WARM_RESET.we = ~pwrgood_toggle_hint;
    end
    else begin
        mci_reg_hwif_in.RESET_REASON.WARM_RESET.we = '0;
    end
end

assign mci_reg_hwif_in.RESET_REASON.WARM_RESET.next = 1'b1;


////////////////////////////////////////////////////////
// MAILBOX 
////////////////////////////////////////////////////////
// Generate a pulse to set the interrupt bit
always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mcu_mbox0_data_avail_d <= '0;
    end  
    else begin
        mcu_mbox0_data_avail_d <= mcu_mbox0_data_avail;
    end  
end

always_comb mcu_mbox0_cmd_avail_p = mcu_mbox0_data_avail & !mcu_mbox0_data_avail_d;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox0_cmd_avail_sts.hwset          = mcu_mbox0_cmd_avail_p;


always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mcu_mbox1_data_avail_d <= '0;
    end  
    else begin
        mcu_mbox1_data_avail_d <= mcu_mbox1_data_avail;
    end  
end

always_comb mcu_mbox1_cmd_avail_p = mcu_mbox1_data_avail & !mcu_mbox1_data_avail_d;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox1_cmd_avail_sts.hwset          = mcu_mbox1_cmd_avail_p;

always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mcu_mbox0_target_user_done_d <= '0;
    end  
    else begin
        mcu_mbox0_target_user_done_d <= mcu_mbox0_target_user_done;
    end  
end

always_comb mcu_mbox0_target_user_done_p = mcu_mbox0_target_user_done & !mcu_mbox0_target_user_done_d;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox0_target_done_sts.hwset   = mcu_mbox0_target_user_done_p;

always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        mcu_mbox1_target_user_done_d <= '0;
    end  
    else begin
        mcu_mbox1_target_user_done_d <= mcu_mbox1_target_user_done;
    end  
end

always_comb mcu_mbox1_target_user_done_p = mcu_mbox1_target_user_done & !mcu_mbox1_target_user_done_d;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox1_target_done_sts.hwset   = mcu_mbox1_target_user_done_p;

always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox0_soc_req_lock_sts.hwset       = soc_req_mbox0_lock;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox1_soc_req_lock_sts.hwset       = soc_req_mbox1_lock;

always_comb mci_reg_hwif_in.intr_block_rf.error0_internal_intr_r.error_mbox0_ecc_unc_sts.hwset  = mbox0_sram_double_ecc_error;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox0_ecc_cor_sts.hwset  = mbox0_sram_single_ecc_error;
always_comb mci_reg_hwif_in.intr_block_rf.error0_internal_intr_r.error_mbox1_ecc_unc_sts.hwset  = mbox1_sram_double_ecc_error;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_mbox1_ecc_cor_sts.hwset  = mbox1_sram_single_ecc_error;


always_ff @(posedge clk or negedge mci_rst_b) begin
    if (~mci_rst_b) begin
        cptra_mbox_data_avail_d <= '0;
    end  
    else begin
        cptra_mbox_data_avail_d <= cptra_mbox_data_avail;
    end  
end

always_comb cptra_mbox_cmd_avail_p = cptra_mbox_data_avail & !cptra_mbox_data_avail_d;
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_cptra_mbox_cmd_avail_sts.hwset          = cptra_mbox_cmd_avail_p;

///////////////////////////////////////////////
// MISC INTERRUPTS
///////////////////////////////////////////////
always_comb mci_reg_hwif_in.intr_block_rf.notif0_internal_intr_r.notif_otp_operation_done_sts.hwset       = intr_otp_operation_done;

///////////////////////////////////////////////
// NMI Vector   
///////////////////////////////////////////////
assign mcu_nmi_vector = mci_reg_hwif_out.MCU_NMI_VECTOR.vec;  

////////////////////////////////////////////////////////
// Write-enables for HW_ERROR_FATAL and HW_ERROR_NON_FATAL
// Also calculate whether or not an unmasked event is being set, so we can
// trigger the SOC interrupt signal
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.we  = mcu_sram_double_ecc_error;
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .we      = nmi_intr;
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_dmi_axi_collision.we  = mcu_sram_dmi_axi_collision_error;
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 FATAL events)
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.next    = 1'b1;
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .next        = 1'b1;
always_comb mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_dmi_axi_collision.next  = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_hw_error_fatal_write = (mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .we      && ~mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_nmi_pin.value && |mci_reg_hwif_in.HW_ERROR_FATAL.nmi_pin     .next) ||
                                            (mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.we  && ~mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_ecc_unc.value && |mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_ecc_unc.next)  ||
                                            (mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_dmi_axi_collision.we  && ~mci_reg_hwif_out.internal_hw_error_fatal_mask.mask_mcu_sram_dmi_axi_collision.value && |mci_reg_hwif_in.HW_ERROR_FATAL.mcu_sram_dmi_axi_collision.next);

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
                                              
                                              
                                              


always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox0_ecc_unc     .we = mbox0_sram_double_ecc_error;
always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox1_ecc_unc     .we = mbox1_sram_double_ecc_error;
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 NON-FATAL events)
always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox0_ecc_unc     .next = 1'b1;
always_comb mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox1_ecc_unc     .next = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_hw_error_non_fatal_write =  
                                                (mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox0_ecc_unc     .we && ~mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox0_ecc_unc     .value && |mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox0_ecc_unc     .next) ||
                                                (mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox1_ecc_unc     .we && ~mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox1_ecc_unc     .value && |mci_reg_hwif_in.HW_ERROR_NON_FATAL.mbox1_ecc_unc     .next);
always_comb unmasked_hw_error_non_fatal_is_set = 
                                                    (mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox0_ecc_unc     .value && ~mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox0_ecc_unc     .value) ||
                                                    (mci_reg_hwif_out.HW_ERROR_NON_FATAL.mbox1_ecc_unc     .value && ~mci_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox1_ecc_unc     .value);

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
        all_error_fatal <= 1'b0;
    end
    // FW write that SETS a new (non-masked) bit results in interrupt assertion
    else if (cif_resp_if.dv &&
             mci_reg_hwif_out.FW_ERROR_FATAL.error_code.swmod &&
             |(cif_resp_if.req_data.wdata & ~mci_reg_hwif_out.internal_fw_error_fatal_mask.mask.value & ~mci_reg_hwif_out.FW_ERROR_FATAL.error_code.value)) begin
        all_error_fatal <= 1'b1;
    end
    // HW event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_hw_error_fatal_write) begin
        all_error_fatal <= 1'b1;
    end
    // AGG event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_agg_error_fatal_write) begin
        all_error_fatal <= 1'b1;
    end
    // NOTE: There is no mechanism to clear interrupt assertion by design.
    //       Platform MUST perform mci_rst_b in order to clear error_fatal
    //       output signal, per the integration spec.
    else begin
        all_error_fatal <= all_error_fatal;
    end
end
always_ff@(posedge clk or negedge mci_rst_b) begin
    if(~mci_rst_b) begin
        all_error_non_fatal <= 1'b0;
    end
    // FW write that SETS a new (non-masked) bit results in interrupt assertion
    else if (cif_resp_if.dv &&
             mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.swmod &&
             |(cif_resp_if.req_data.wdata & ~mci_reg_hwif_out.internal_fw_error_non_fatal_mask.mask.value  & ~mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.value)) begin
        all_error_non_fatal <= 1'b1;
    end
    // HW event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_hw_error_non_fatal_write) begin
        all_error_non_fatal <= 1'b1;
    end
    // AGG event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_agg_error_non_fatal_write) begin
        all_error_non_fatal <= 1'b1;
    end
    // If FW performs a write that clears all outstanding (unmasked) ERROR_NON_FATAL events, deassert interrupt
    else if (~unmasked_hw_error_non_fatal_is_set && ~unmasked_agg_error_non_fatal_is_set && 
             ~|(~mci_reg_hwif_out.internal_fw_error_non_fatal_mask.mask.value & mci_reg_hwif_out.FW_ERROR_NON_FATAL.error_code.value)) begin
        all_error_non_fatal <= 1'b0;
    end
    else begin
        all_error_non_fatal <= all_error_non_fatal;
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
assign wdt_timer2_timeout_serviced = error_wdt_timer2_timeout_sts_prev & ~mci_reg_hwif_out.intr_block_rf.error0_internal_intr_r.error_wdt_timer2_timeout_sts.value;


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
        .rst  ('0), 

        .s_cpuif_req            (cif_resp_if.dv),
        .s_cpuif_req_is_wr      (cif_resp_if.req_data.write),
        .s_cpuif_addr           (cif_resp_if.req_data.addr[MCI_REG_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data        (cif_resp_if.req_data.wdata),
        .s_cpuif_wr_biten       (c_cpuif_wr_biten),
        .s_cpuif_req_stall_wr   (),  
        .s_cpuif_req_stall_rd   (),  
        .s_cpuif_rd_ack         (),  
        .s_cpuif_rd_err         (mci_reg_read_error),
        .s_cpuif_rd_data        (cif_resp_if.rdata),   
        .s_cpuif_wr_ack         (),    
        .s_cpuif_wr_err         (mci_reg_write_error),

        .hwif_in                (mci_reg_hwif_in),
        .hwif_out               (mci_reg_hwif_out)

);


endmodule
