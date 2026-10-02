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
// MCI boot FSM glitch test (+cptra_ss_sv_test=MCI_BOOT_FSM_GLITCH)
//
// For each of the 12 normal MCI boot FSM states, in boot order:
//   1. Warm-boot the subsystem and drive it naturally (breakpoint strap, AXI
//      register writes, real MCU halt handshake) until the FSM is in the
//      target state.
//   2. Replace the sparse state flop's next-state input with a random invalid
//      12-bit encoding for exactly one clock edge.
//   3. Check: the invalid code is detected, the FSM enters BOOT_ERROR, MCU and
//      Caliptra are held in reset while the subsystem stays out of reset,
//      cptra_ss_all_error_fatal_o asserts, HW_FLOW_STATUS reads 0xF and
//      HW_ERROR_FATAL reads exactly fsm_error.
//   4. Warm reset: all_error_fatal (reset by cptra_ss_rst_b_o) must clear,
//      while HW_ERROR_FATAL.fsm_error (reset by power-good) must be retained.
//   5. Reboot to the breakpoint, clear fsm_error with an AXI W1C and check it
//      stays clear without re-asserting all_error_fatal.
//   Only then does the test move to the next target state.
//
// Injection point: u_boot_state_regs_d is the input of the
// CALIPTRA_PRIM_FLOP_SPARSE_FSM macro. In simulation it feeds both the
// behavioral state flop and the caliptra_prim_sparse_fsm_flop copy, so forcing
// it keeps the macro's equality assertion valid. It sits after the warm-reset
// mux, so injection is only done while the internal warm_reset is low.
//
// MCU: no MCU firmware needs to run. The MCU halt request input is held high
// for the whole test, so the MCU halts as soon as it leaves reset. Injections
// with the MCU out of reset wait for it to report halted, so it is never reset
// in the middle of a bus transfer. Caliptra never receives fuse-done, so its
// CPU never runs.
//------------------------------------------------------------------------------

`define MCI_BFG_SEQR `MCI_PATH.i_boot_seqr

localparam int MCI_BFG_NUM_CASES = 12;

// Per-phase watchdog budgets, in core_clk cycles
localparam int MCI_BFG_BOOT_BUDGET  = 1_000_000; // boot and state traversal
localparam int MCI_BFG_AXI_BUDGET   = 10_000;    // a few AXI register accesses
localparam int MCI_BFG_RESET_BUDGET = 32;        // warm reset -> IDLE and fatal output cleared
localparam int MCI_BFG_FATAL_BUDGET = 16;        // BOOT_ERROR -> cptra_ss_all_error_fatal_o
localparam int MCI_BFG_RESET_HOLD   = 16;        // warm reset hold time
localparam int MCI_BFG_SETTLE       = 8;         // register pipeline settle time

// Test phases, visible in waves as mci_bfg_phase
typedef enum logic [3:0] {
    MCI_BFG_PH_INIT        = 4'h0,
    MCI_BFG_PH_BASELINE    = 4'h1,
    MCI_BFG_PH_WARM_RESET  = 4'h2,
    MCI_BFG_PH_TARGET      = 4'h3,
    MCI_BFG_PH_INJECT      = 4'h4,
    MCI_BFG_PH_ERROR_CHECK = 4'h5,
    MCI_BFG_PH_REBOOT      = 4'h6,
    MCI_BFG_PH_RETAINED    = 4'h7,
    MCI_BFG_PH_W1C         = 4'h8,
    MCI_BFG_PH_DONE        = 4'h9
} mci_bfg_phase_e;

// Source states, in boot order
mci_pkg::mci_boot_fsm_state_e mci_bfg_targets [MCI_BFG_NUM_CASES] = '{
    mci_pkg::BOOT_IDLE,
    mci_pkg::BOOT_OTP_FC,
    mci_pkg::BOOT_LCC,
    mci_pkg::BOOT_BREAKPOINT_CHECK,
    mci_pkg::BOOT_BREAKPOINT,
    mci_pkg::BOOT_MCU,
    mci_pkg::BOOT_WAIT_CPTRA_GO,
    mci_pkg::BOOT_CPTRA,
    mci_pkg::BOOT_WAIT_MCU_RST_REQ,
    mci_pkg::BOOT_HALT_MCU,
    mci_pkg::BOOT_WAIT_MCU_HALTED,
    mci_pkg::BOOT_RST_MCU
};

// Test progress, visible in waves
mci_bfg_phase_e                               mci_bfg_phase          = MCI_BFG_PH_INIT;
int                                           mci_bfg_case_num       = 0;
mci_pkg::mci_boot_fsm_state_e                 mci_bfg_target         = mci_pkg::BOOT_IDLE;
logic [mci_pkg::MCI_BOOT_FSM_STATE_WIDTH-1:0] mci_bfg_injected_code  = '0;
logic [mci_pkg::MCI_BOOT_FSM_STATE_WIDTH-1:0] mci_bfg_codes [MCI_BFG_NUM_CASES];
logic                                         mci_bfg_inject_active  = 1'b0;
logic                                         mci_bfg_error_expected = 1'b0;
logic [MCI_BFG_NUM_CASES-1:0]                 mci_bfg_pass_mask      = '0;
int                                           mci_bfg_phase_budget   = 0;
int                                           mci_bfg_phase_cycles   = 0;
bit                                           mci_bfg_running        = 1'b0;

// The right-hand side of the injection force comes from the bound helper
// u_mci_boot_fsm_glitch_inject (mci_boot_fsm_glitch_inject.sv). The RTL and TB
// libraries each compile their own mci_pkg, so a TB enum value is not
// assignment compatible with the RTL state signal; the helper's value has the
// RTL type.
`define MCI_BFG_HELPER `MCI_BFG_SEQR.u_mci_boot_fsm_glitch_inject

function automatic string mci_bfg_state_name(logic [mci_pkg::MCI_BOOT_FSM_STATE_WIDTH-1:0] code);
    mci_pkg::mci_boot_fsm_state_e s = mci_pkg::mci_boot_fsm_state_e'(code);
    string n = s.name();
    return (n == "") ? "INVALID" : n;
endfunction

function automatic void mci_bfg_set_phase(mci_bfg_phase_e ph, int budget);
    mci_bfg_phase        = ph;
    mci_bfg_phase_budget = budget;
    mci_bfg_phase_cycles = 0;
endfunction

// MCU is in reset, or out of reset and halted
function automatic bit mci_bfg_mcu_quiescent();
    return (`MCU_PATH.rst_l !== 1'b1) || (cptra_ss_mcu_halt_status_o === 1'b1);
endfunction

function automatic void mci_bfg_print_status(string tag);
    $display("[%t] MCI_BFG %s: case %0d/%0d target=%s phase=%s boot_fsm=%s(0x%03h) warm_reset=%b fsm_error=%b cptra_ss_rst_b_o=%b mcu_rst_b=%b cptra_rst_b=%b all_error_fatal_o=%b mcu_halted=%b pwrgood=%b",
             $time, tag, mci_bfg_case_num, MCI_BFG_NUM_CASES, mci_bfg_target.name(), mci_bfg_phase.name(),
             mci_bfg_state_name(`MCI_BFG_SEQR.boot_fsm), `MCI_BFG_SEQR.boot_fsm,
             `MCI_BFG_SEQR.warm_reset, `MCI_BFG_SEQR.fsm_error,
             `MCI_PATH.cptra_ss_rst_b_o, `MCI_PATH.mcu_rst_b, `MCI_PATH.cptra_rst_b,
             `CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o, cptra_ss_mcu_halt_status_o, cptra_pwrgood);
endfunction

task automatic mci_bfg_fail(string msg);
    if (mci_bfg_inject_active) begin
        release `MCI_BFG_SEQR.u_boot_state_regs_d;
        mci_bfg_inject_active = 1'b0;
    end
    mci_bfg_print_status("FAIL_STATE");
    $display("[%t] MCI_BFG passed-state mask so far: %b", $time, mci_bfg_pass_mask);
    $fatal(1, "[%t] MCI_BFG FAIL: case %0d/%0d target=%s injected=0x%03h: %s",
           $time, mci_bfg_case_num, MCI_BFG_NUM_CASES, mci_bfg_target.name(), mci_bfg_injected_code, msg);
endtask

// Background checker: per-phase watchdog, and no boot FSM error or fatal
// output unless an injection is armed.
task automatic mci_bfg_monitor();
    forever begin
        @(negedge core_clk);
        if (!mci_bfg_running) continue;
        mci_bfg_phase_cycles++;
        if (mci_bfg_phase_cycles > mci_bfg_phase_budget)
            mci_bfg_fail($sformatf("timeout: phase %s exceeded %0d core_clk cycles", mci_bfg_phase.name(), mci_bfg_phase_budget));
        if (!mci_bfg_error_expected && (`MCI_BFG_SEQR.fsm_error !== 1'b0))
            mci_bfg_fail("boot FSM error while no injection was armed");
        if (!mci_bfg_error_expected && (`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o !== 1'b0))
            mci_bfg_fail("cptra_ss_all_error_fatal_o asserted while no injection was armed");
    end
endtask

task automatic mci_bfg_axi_read(input logic [AXI_AW-1:0] addr, input string name, output logic [31:0] data);
    axi_resp_e resp;
    bfm_axi_read_single_response(addr, cptra_ss_strap_mci_soc_config_axi_user_i, data, resp);
    if (resp !== AXI_RESP_OKAY)
        mci_bfg_fail($sformatf("AXI read of %s returned response %0d", name, resp));
    if ($isunknown(data))
        mci_bfg_fail($sformatf("AXI read of %s returned unknown data 0x%08h", name, data));
endtask

task automatic mci_bfg_axi_write(input logic [AXI_AW-1:0] addr, input string name, input logic [31:0] data);
    axi_resp_e resp;
    bfm_axi_write_single_response(addr, cptra_ss_strap_mci_soc_config_axi_user_i, data, resp);
    if (resp !== AXI_RESP_OKAY)
        mci_bfg_fail($sformatf("AXI write of 0x%08h to %s returned response %0d", data, name, resp));
endtask

task automatic mci_bfg_axi_expect(input logic [AXI_AW-1:0] addr, input string name, input logic [31:0] mask, input logic [31:0] exp);
    logic [31:0] data;
    mci_bfg_axi_read(addr, name, data);
    if ((data & mask) !== exp)
        mci_bfg_fail($sformatf("%s: read 0x%08h, (data & 0x%08h) = 0x%08h, expected 0x%08h", name, data, mask, data & mask, exp));
    $display("[%t] MCI_BFG   %s = 0x%08h (expected 0x%08h under mask 0x%08h)", $time, name, data, exp, mask);
endtask

// Pick a random 12-bit value that is not any named state, including BOOT_ERROR
task automatic mci_bfg_pick_invalid_code(output logic [mci_pkg::MCI_BOOT_FSM_STATE_WIDTH-1:0] code);
    bit [mci_pkg::MCI_BOOT_FSM_STATE_WIDTH-1:0] v;
    mci_pkg::mci_boot_fsm_state_e s;
    if (!std::randomize(v) with {
            !(v inside {mci_pkg::BOOT_IDLE, mci_pkg::BOOT_OTP_FC, mci_pkg::BOOT_LCC,
                        mci_pkg::BOOT_BREAKPOINT_CHECK, mci_pkg::BOOT_BREAKPOINT, mci_pkg::BOOT_MCU,
                        mci_pkg::BOOT_WAIT_CPTRA_GO, mci_pkg::BOOT_CPTRA, mci_pkg::BOOT_WAIT_MCU_RST_REQ,
                        mci_pkg::BOOT_HALT_MCU, mci_pkg::BOOT_WAIT_MCU_HALTED, mci_pkg::BOOT_RST_MCU,
                        mci_pkg::BOOT_ERROR});
        })
        mci_bfg_fail("std::randomize could not pick an invalid boot FSM encoding");
    // Independent check against every named encoding
    s = s.first();
    repeat (s.num()) begin
        if (v == s)
            mci_bfg_fail($sformatf("random code 0x%03h matches named state %s", v, s.name()));
        s = s.next();
    end
    code = v;
endtask

task automatic mci_bfg_wait_state(mci_pkg::mci_boot_fsm_state_e st);
    do @(negedge core_clk); while (`MCI_BFG_SEQR.boot_fsm !== st);
endtask

task automatic mci_bfg_wait_mcu_halted();
    $display("[%t] MCI_BFG   waiting for MCU to report halted (halt request held by TB)", $time);
    do @(negedge core_clk); while (cptra_ss_mcu_halt_status_o !== 1'b1);
endtask

// Normal-flow stimulus that moves the FSM from reset toward the target state.
// Runs in parallel with mci_bfg_inject, which catches the target state.
task automatic mci_bfg_drive_to(mci_pkg::mci_boot_fsm_state_e target);
    // IDLE through BREAKPOINT are reached by the normal boot sequence (the
    // breakpoint strap is set), so no stimulus is needed.
    if (target inside {mci_pkg::BOOT_IDLE, mci_pkg::BOOT_OTP_FC, mci_pkg::BOOT_LCC,
                       mci_pkg::BOOT_BREAKPOINT_CHECK, mci_pkg::BOOT_BREAKPOINT})
        return;

    // Release the breakpoint: BOOT_MCU (one cycle) -> BOOT_WAIT_CPTRA_GO, MCU leaves reset
    mci_bfg_wait_state(mci_pkg::BOOT_BREAKPOINT);
    $display("[%t] MCI_BFG   writing MCI_BOOTFSM_GO", $time);
    mci_bfg_axi_write(`SOC_MCI_TOP_MCI_REG_MCI_BOOTFSM_GO, "MCI_BOOTFSM_GO", `MCI_REG_MCI_BOOTFSM_GO_GO_MASK);
    if (target inside {mci_pkg::BOOT_MCU, mci_pkg::BOOT_WAIT_CPTRA_GO})
        return;

    // Let the MCU halt before any later transition
    mci_bfg_wait_state(mci_pkg::BOOT_WAIT_CPTRA_GO);
    mci_bfg_wait_mcu_halted();
    // BOOT_CPTRA (one cycle) -> BOOT_WAIT_MCU_RST_REQ
    $display("[%t] MCI_BFG   writing CPTRA_BOOT_GO", $time);
    mci_bfg_axi_write(`SOC_MCI_TOP_MCI_REG_CPTRA_BOOT_GO, "CPTRA_BOOT_GO", `MCI_REG_CPTRA_BOOT_GO_GO_MASK);
    if (target inside {mci_pkg::BOOT_CPTRA, mci_pkg::BOOT_WAIT_MCU_RST_REQ})
        return;

    // Request an MCU reset: BOOT_HALT_MCU -> BOOT_WAIT_MCU_HALTED -> BOOT_RST_MCU.
    // The MCU is already halted, so each halt-handshake state lasts one cycle.
    // BOOT_RST_MCU then holds because the FW execution region lock stays clear.
    mci_bfg_wait_state(mci_pkg::BOOT_WAIT_MCU_RST_REQ);
    $display("[%t] MCI_BFG   writing RESET_REQUEST.mcu_req", $time);
    mci_bfg_axi_write(`SOC_MCI_TOP_MCI_REG_RESET_REQUEST, "RESET_REQUEST", `MCI_REG_RESET_REQUEST_MCU_REQ_MASK);
endtask

// Catch the target state, inject the invalid code for one clock, and do the
// cycle-accurate checks. All sampling is on falling edges so registered
// values have settled.
task automatic mci_bfg_inject(mci_pkg::mci_boot_fsm_state_e target);
    int i;

    // The warm-reset mux sits before the injection point, so only inject while
    // warm_reset is low. For BOOT_IDLE this is the single cycle between warm
    // reset release and the first IDLE -> OTP_FC transition.
    do @(negedge core_clk);
    while (!((`MCI_BFG_SEQR.boot_fsm === target) && (`MCI_BFG_SEQR.warm_reset === 1'b0) &&
             (cptra_pwrgood === 1'b1) && mci_bfg_mcu_quiescent()));

    mci_bfg_set_phase(MCI_BFG_PH_INJECT, 4);
    $display("[%t] MCI_BFG INJECT: case %0d/%0d in %s, normal next state %s, forcing next state to invalid 0x%03h for one clock",
             $time, mci_bfg_case_num, MCI_BFG_NUM_CASES, target.name(),
             mci_bfg_state_name(`MCI_BFG_SEQR.boot_fsm_d), mci_bfg_injected_code);
    mci_bfg_error_expected = 1'b1;
    `MCI_BFG_HELPER.set_code(mci_bfg_injected_code);
    mci_bfg_inject_active  = 1'b1;
    force `MCI_BFG_SEQR.u_boot_state_regs_d = `MCI_BFG_HELPER.force_val;
    @(posedge core_clk); // both state flop copies sample the invalid code here
    @(negedge core_clk);
    release `MCI_BFG_SEQR.u_boot_state_regs_d;
    mci_bfg_inject_active = 1'b0;

    // The invalid code is the present state and is detected combinationally
    if (`MCI_BFG_SEQR.boot_fsm !== mci_bfg_injected_code)
        mci_bfg_fail($sformatf("boot_fsm is 0x%03h after injection, expected injected code 0x%03h", `MCI_BFG_SEQR.boot_fsm, mci_bfg_injected_code));
    if (`MCI_BFG_SEQR.fsm_error !== 1'b1)
        mci_bfg_fail("fsm_error not asserted while boot_fsm holds the invalid code");
    if (`MCI_BFG_SEQR.boot_fsm_encoded !== 4'hF)
        mci_bfg_fail($sformatf("boot_fsm_encoded is 0x%0h for the invalid code, expected 0xF", `MCI_BFG_SEQR.boot_fsm_encoded));

    // Next edge: BOOT_ERROR with registered containment
    @(negedge core_clk);
    if (`MCI_BFG_SEQR.boot_fsm !== mci_pkg::BOOT_ERROR)
        mci_bfg_fail("FSM did not enter BOOT_ERROR one clock after the invalid code");
    if ((`MCI_PATH.mcu_rst_b !== 1'b0) || (`MCI_PATH.cptra_rst_b !== 1'b0) || (`MCI_PATH.cptra_ss_rst_b_o !== 1'b1))
        mci_bfg_fail("BOOT_ERROR containment wrong: expected mcu_rst_b=0 cptra_rst_b=0 cptra_ss_rst_b_o=1");
    $display("[%t] MCI_BFG ERROR_CONFIRMED: BOOT_ERROR entered, MCU and Caliptra held in reset, subsystem out of reset", $time);

    // The fatal output asserts, and BOOT_ERROR holds with the force released
    mci_bfg_set_phase(MCI_BFG_PH_ERROR_CHECK, MCI_BFG_FATAL_BUDGET + 4);
    for (i = 0; i < MCI_BFG_FATAL_BUDGET; i++) begin
        if (`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o === 1'b1) break;
        @(negedge core_clk);
        if (`MCI_BFG_SEQR.boot_fsm !== mci_pkg::BOOT_ERROR)
            mci_bfg_fail("FSM left BOOT_ERROR without a reset");
    end
    if (`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o !== 1'b1)
        mci_bfg_fail($sformatf("cptra_ss_all_error_fatal_o not asserted within %0d cycles of BOOT_ERROR", MCI_BFG_FATAL_BUDGET));
    $display("[%t] MCI_BFG ERROR_CONFIRMED: cptra_ss_all_error_fatal_o asserted %0d cycle(s) after BOOT_ERROR", $time, i);
endtask

// Register-level checks while the FSM is in BOOT_ERROR
task automatic mci_bfg_check_error_status();
    mci_bfg_set_phase(MCI_BFG_PH_ERROR_CHECK, MCI_BFG_AXI_BUDGET);
    mci_bfg_axi_expect(`SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS, "HW_FLOW_STATUS", `MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK,
                       32'hF << `MCI_REG_HW_FLOW_STATUS_BOOT_FSM_LOW);
    // Whole register, so any other fatal source also fails the check
    mci_bfg_axi_expect(`SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", 32'hFFFF_FFFF, `MCI_REG_HW_ERROR_FATAL_FSM_ERROR_MASK);
    if ((`MCI_BFG_SEQR.boot_fsm !== mci_pkg::BOOT_ERROR) || (`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o !== 1'b1))
        mci_bfg_fail("BOOT_ERROR or cptra_ss_all_error_fatal_o did not persist during register checks");
    $display("[%t] MCI_BFG ERROR_CONFIRMED: HW_FLOW_STATUS=0xF and HW_ERROR_FATAL.fsm_error=1 over AXI", $time);
endtask

// Assert warm reset, check the FSM returns to IDLE with the subsystem held in
// reset and the fatal output cleared, and hold reset. Power-good stays high.
// The MCU is already in reset or halted, so this deliberately does not use the
// BFM reset service, which first runs an MCU halt handshake.
task automatic mci_bfg_warm_reset_assert(string why);
    int i;
    mci_bfg_set_phase(MCI_BFG_PH_WARM_RESET, MCI_BFG_RESET_BUDGET + MCI_BFG_RESET_HOLD + 8);
    @(negedge core_clk);
    $display("[%t] MCI_BFG WARM_RESET: asserting warm reset (%s)", $time, why);
    assert_cptra_rst_b(0, 0);
    for (i = 0; i < MCI_BFG_RESET_BUDGET; i++) begin
        @(negedge core_clk);
        if ((`MCI_BFG_SEQR.boot_fsm === mci_pkg::BOOT_IDLE) && (`MCI_PATH.cptra_ss_rst_b_o === 1'b0) &&
            (`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o === 1'b0))
            break;
    end
    if (i == MCI_BFG_RESET_BUDGET)
        mci_bfg_fail($sformatf("warm reset did not reach IDLE with cptra_ss_rst_b_o=0 and all_error_fatal_o=0 within %0d cycles", MCI_BFG_RESET_BUDGET));
    $display("[%t] MCI_BFG WARM_RESET: FSM in IDLE, subsystem in reset, cptra_ss_all_error_fatal_o=0 after %0d cycle(s)", $time, i + 1);
    repeat (MCI_BFG_RESET_HOLD) begin
        @(negedge core_clk);
        if (cptra_pwrgood !== 1'b1)
            mci_bfg_fail("power-good dropped during warm reset");
        if (`MCI_BFG_SEQR.boot_fsm !== mci_pkg::BOOT_IDLE)
            mci_bfg_fail("FSM left IDLE while warm reset was held");
    end
    if (`MCI_BFG_SEQR.fsm_error !== 1'b0)
        mci_bfg_fail("fsm_error still asserted in IDLE");
    mci_bfg_error_expected = 1'b0;
endtask

// Recover from BOOT_ERROR: warm reset, reboot to the breakpoint, confirm the
// retained status, then clear it with W1C.
task automatic mci_bfg_recover();
    mci_bfg_warm_reset_assert("recovery");

    mci_bfg_set_phase(MCI_BFG_PH_REBOOT, MCI_BFG_BOOT_BUDGET);
    deassert_cptra_rst_b(0, 0);
    mci_bfg_wait_state(mci_pkg::BOOT_BREAKPOINT);
    repeat (MCI_BFG_SETTLE) @(negedge core_clk);
    $display("[%t] MCI_BFG REBOOT: back at BOOT_BREAKPOINT", $time);

    // The status bit is reset only by power-good, so it survives the warm reset
    mci_bfg_set_phase(MCI_BFG_PH_RETAINED, MCI_BFG_AXI_BUDGET);
    mci_bfg_axi_expect(`SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", 32'hFFFF_FFFF, `MCI_REG_HW_ERROR_FATAL_FSM_ERROR_MASK);
    $display("[%t] MCI_BFG RETAINED_STATUS: HW_ERROR_FATAL.fsm_error survived warm reset; fsm_error and all_error_fatal_o are low", $time);

    mci_bfg_set_phase(MCI_BFG_PH_W1C, MCI_BFG_AXI_BUDGET);
    mci_bfg_axi_write(`SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", `MCI_REG_HW_ERROR_FATAL_FSM_ERROR_MASK);
    mci_bfg_axi_expect(`SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", 32'hFFFF_FFFF, 32'h0);
    // A cleared status bit must stay cleared and must not re-assert the fatal output
    repeat (MCI_BFG_SETTLE) @(negedge core_clk);
    mci_bfg_axi_expect(`SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", 32'hFFFF_FFFF, 32'h0);
    if (`CPTRA_SS_TOP_PATH.cptra_ss_all_error_fatal_o !== 1'b0)
        mci_bfg_fail("cptra_ss_all_error_fatal_o asserted after fsm_error was cleared");
    $display("[%t] MCI_BFG W1C_CLEAR: HW_ERROR_FATAL cleared to 0x0 and stays clear", $time);
endtask

task automatic mci_boot_fsm_glitch();
    int idx;

    $display("[%t] MCI_BFG: MCI boot FSM glitch test start", $time);
    $display("[%t] MCI_BFG: for each of %0d boot states inject one random invalid encoding, then check", $time, MCI_BFG_NUM_CASES);
    $display("[%t] MCI_BFG:   1) all_error_fatal pin asserts  2) HW_ERROR_FATAL.fsm_error=1", $time);
    $display("[%t] MCI_BFG:   3) warm reset clears the pin, keeps the status  4) AXI W1C clears the status", $time);

    // Halt the MCU whenever it leaves reset; no MCU firmware needs to run
    force `MCU_PATH.i_cpu_halt_req = 1'b1;
    $display("[%t] MCI_BFG: holding MCU halt request high for the whole test", $time);

    fork
        mci_bfg_monitor();
    join_none

    wait (cptra_pwrgood === 1'b1);
    @(negedge core_clk);
    mci_bfg_running = 1'b1;

    // Baseline: first boot reaches the breakpoint with no errors
    mci_bfg_set_phase(MCI_BFG_PH_BASELINE, MCI_BFG_BOOT_BUDGET);
    mci_bfg_wait_state(mci_pkg::BOOT_BREAKPOINT);
    repeat (MCI_BFG_SETTLE) @(negedge core_clk);
    $display("[%t] MCI_BFG BASELINE: first boot reached BOOT_BREAKPOINT", $time);
    mci_bfg_set_phase(MCI_BFG_PH_BASELINE, MCI_BFG_AXI_BUDGET);
    mci_bfg_axi_expect(`SOC_MCI_TOP_MCI_REG_HW_FLOW_STATUS, "HW_FLOW_STATUS", `MCI_REG_HW_FLOW_STATUS_BOOT_FSM_MASK,
                       32'(mci_pkg::mci_boot_fsm_state_encode(mci_pkg::BOOT_BREAKPOINT)) << `MCI_REG_HW_FLOW_STATUS_BOOT_FSM_LOW);
    mci_bfg_axi_expect(`SOC_MCI_TOP_MCI_REG_HW_ERROR_FATAL, "HW_ERROR_FATAL", 32'hFFFF_FFFF, 32'h0);

    for (idx = 0; idx < MCI_BFG_NUM_CASES; idx++) begin
        mci_bfg_case_num = idx + 1;
        mci_bfg_target   = mci_bfg_targets[idx];
        mci_bfg_pick_invalid_code(mci_bfg_injected_code);
        mci_bfg_codes[idx] = mci_bfg_injected_code;
        $display("[%t] MCI_BFG TARGET: ===== case %0d/%0d: source state %s (0x%03h), invalid code 0x%03h =====",
                 $time, mci_bfg_case_num, MCI_BFG_NUM_CASES, mci_bfg_target.name(), mci_bfg_target, mci_bfg_injected_code);

        // Fresh warm boot from the clean breakpoint. The injector is armed
        // before reset release so early and one-cycle states are not missed.
        mci_bfg_warm_reset_assert("launch");
        mci_bfg_set_phase(MCI_BFG_PH_TARGET, MCI_BFG_BOOT_BUDGET);
        fork
            mci_bfg_inject(mci_bfg_target);
            begin
                deassert_cptra_rst_b(0, 0);
                mci_bfg_drive_to(mci_bfg_target);
            end
        join

        mci_bfg_check_error_status();
        mci_bfg_recover();

        mci_bfg_pass_mask[idx] = 1'b1;
        $display("[%t] MCI_BFG CASE_PASS: case %0d/%0d (%s) passed, pass mask %b",
                 $time, mci_bfg_case_num, MCI_BFG_NUM_CASES, mci_bfg_target.name(), mci_bfg_pass_mask);
    end

    mci_bfg_set_phase(MCI_BFG_PH_DONE, MCI_BFG_BOOT_BUDGET);
    if (mci_bfg_pass_mask !== '1)
        mci_bfg_fail($sformatf("not all states passed, pass mask %b", mci_bfg_pass_mask));
    $display("[%t] MCI_BFG SUMMARY: %0d/%0d source states passed, pass mask %b", $time, $countones(mci_bfg_pass_mask), MCI_BFG_NUM_CASES, mci_bfg_pass_mask);
    for (idx = 0; idx < MCI_BFG_NUM_CASES; idx++)
        $display("[%t] MCI_BFG SUMMARY:   case %0d %s injected 0x%03h", $time, idx + 1, mci_bfg_targets[idx].name(), mci_bfg_codes[idx]);

    mci_bfg_running = 1'b0;
    release `MCU_PATH.i_cpu_halt_req;
    end_test_successful_req();
endtask

`undef MCI_BFG_HELPER
`undef MCI_BFG_SEQR
