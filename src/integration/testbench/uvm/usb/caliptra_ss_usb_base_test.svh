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

`ifndef CALIPTRA_SS_USB_BASE_TEST_SV
`define CALIPTRA_SS_USB_BASE_TEST_SV

// =============================================================================
// Base test for the Caliptra SS USB VIP environment.
//
// This test:
// - Creates caliptra_ss_usb_env with one VIP host_agent.
// - Configures host_cfg for the local HS host stack.
// - Configures dev_cfg as the template for host_agent.remote_cfg, the modeled
//   device PHY attached to the DUT UTMI+ interface.
// - Monitors the MCU halt status signal (cptra_ss_mcu_halt_status_o) in
//   run_phase via phase_ready_to_end(). The run_phase objection is held until
//   the MCU firmware asserts halt or a timeout expires (test fails on timeout).
//   This prevents outstanding AXI transactions from the MCU causing assertion
//   failures in the AXI interconnect after the UVM environment tears down.
//
// MCU HALT TIMEOUT SIZING (@ ~25 ns per poll iteration on a 400 MHz MCU):
//   The default timeout is 100 ms (100_000_000 ns) which safely covers all
//   USB tests. Worst-case poll budgets by test:
//
//     caliptra_ss_usb_init             20 000 iters x 1 loop  ~  0.5 ms
//     caliptra_ss_usb_hs_conn          30 000 iters x 1 loop  ~  0.75 ms
//     caliptra_ss_usb_hs_dev_bulk_out  30 000 iters x 1 loop  ~  0.75 ms
//     caliptra_ss_usb_fs_dev_bulk_*    50 000 iters x 1 loop  ~  1.25 ms
//     caliptra_ss_usb_usbd_conn        50 000 iters x 1 loop  ~  1.25 ms
//     caliptra_ss_usb_hs_dev_remote_*  50 000 iters x 1 loop  ~  1.25 ms
//     caliptra_ss_usb_hs_dev_resume   100 000 iters x 1 loop  ~  2.5  ms
//     caliptra_ss_usb_hs_dev_iso_out  100 000 iters x 1 loop  ~  2.5  ms
//     caliptra_ss_usb_hs_dev_powerdown 200 000 iters x 1 loop ~  5    ms
//     caliptra_ss_usb_hs_host_bulk_out  (500k + 200k + 200k)  ~ 22    ms
//     caliptra_ss_usb_hs_host_iso_out   (500k x 4 + 200k x 2) ~ 35    ms
//     caliptra_ss_usb_hs_dev_disconnect 500 000 iters x 3 loops~ 37.5 ms
//     caliptra_ss_usb_hs_dev_nbyte    2 000 000 iters x 1 loop~ 50    ms
//     caliptra_ss_usb_hs_host_remote* (2M SOF + spin delays)  ~ 60+   ms
//     caliptra_ss_usb_fs_clock        (no heavy poll loop)    ~  1    ms
//
//   Tests that extend caliptra_ss_usb_base_test can call
//   get_mcu_halt_timeout() override to return a tighter value if needed.
// =============================================================================

class caliptra_ss_usb_base_test extends uvm_test;

    `uvm_component_utils(caliptra_ss_usb_base_test)

    caliptra_ss_usb_env        env;
    caliptra_ss_usb_shared_cfg cfg;

    function new(string name = "caliptra_ss_usb_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Virtual interface handle for the bfm_services_if.
    // Set in build_phase from uvm_config_db; used in phase_ready_to_end()
    // to monitor mcu_halt_status without a cross-module hierarchical reference.
    virtual caliptra_ss_bfm_services_if bfm_if;

    // One-shot guard: phase_ready_to_end() is called repeatedly by UVM each
    // time it re-evaluates whether the run_phase can end. Without this flag
    // every call would raise a new objection and spawn a new monitor task,
    // creating an infinite raise/drop loop. The flag ensures the objection is
    // raised and the task spawned exactly once.
    bit mcu_halt_monitor_started = 1'b0;

    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void end_of_elaboration_phase(uvm_phase phase);
    extern virtual function void phase_ready_to_end(uvm_phase phase);
    extern virtual function void final_phase(uvm_phase phase);

    // Task that does the actual MCU halt wait + timeout. Called from within
    // the fork/join_none in phase_ready_to_end(). Keeping it as a task allows
    // the named-block disable statements to work correctly (SV LRM sec 10.3
    // forbids disable of non-enclosing blocks inside a function).
    // The task also owns the run_phase objection so that it works regardless
    // of whether a derived test calls super.run_phase() or not.
    extern virtual task          mcu_halt_monitor_task(uvm_phase phase);

    // -------------------------------------------------------------------------
    // get_mcu_halt_timeout
    //
    // Returns the maximum simulation time (as a 'time' value in ns resolution)
    // to wait for cptra_ss_mcu_halt_status_o after the UVM sequences complete.
    //
    // The default of 100 ms covers the heaviest USB test firmware poll budgets.
    // Override in a derived test to use a tighter guard where appropriate:
    //
    //   virtual function time get_mcu_halt_timeout();
    //       return 5_000_000ns;  // 5 ms for fast tests
    //   endfunction
    //
    // Per-test guidance (see class header comment for full analysis):
    //   Fast tests  (usb_init, hs_conn, bulk_out, remote_wakeup): 5 ms
    //   Medium tests (dev_resume, dev_iso_out, dev_powerdown):    10 ms
    //   Heavy tests  (host_bulk_out, host_iso_out, disconnect):   50 ms
    //   Heaviest     (hs_dev_nbyte, hs_host_remotewakeup):       100 ms
    // -------------------------------------------------------------------------
    virtual function time get_mcu_halt_timeout();
        return 100_000_000ns;  // 100 ms -- safe default for all USB tests
    endfunction

endclass

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_base_test::build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    // Create the shared host/remote PHY configuration.
    cfg = caliptra_ss_usb_shared_cfg::type_id::create("cfg", this);
    cfg.setup_usb_20_utmi_host_defaults();

    // Pass configuration to env.
    uvm_config_db#(caliptra_ss_usb_shared_cfg)::set(this, "env", "cfg", cfg);

    // Create environment.
    env = caliptra_ss_usb_env::type_id::create("env", this);

    // Retrieve the bfm_services_if virtual interface handle so that
    // phase_ready_to_end() can monitor mcu_halt_status without a
    // cross-module hierarchical reference (XMRE) from within this package.
    if (!uvm_config_db#(virtual caliptra_ss_bfm_services_if)::get(
            this, "", "bfm_services_if", bfm_if))
        `uvm_fatal("build_phase",
            "Failed to get bfm_services_if from uvm_config_db. Ensure the TB top sets it.")

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_base_test::end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    super.end_of_elaboration_phase(phase);
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
endfunction

// -----------------------------------------------------------------------------
// phase_ready_to_end: raise an objection to hold the run_phase, then spawn
// the MCU halt monitor task in a detached thread. Raising the objection here
// (rather than in run_phase) ensures the mechanism works correctly whether or
// not a derived test calls super.run_phase(). The monitor task drops the
// objection once MCU halt is detected or the timeout expires.
//
// The actual wait/timeout/objection-drop logic lives in mcu_halt_monitor_task
// so that named-block disable statements are legal (functions cannot disable
// non-enclosing blocks per SV LRM sec 10.3).
// -----------------------------------------------------------------------------
function void caliptra_ss_usb_base_test::phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() != "run") return;
    // Guard: only raise the objection and spawn the monitor once.
    // phase_ready_to_end() is called repeatedly by UVM each time it checks
    // whether the run_phase can end. Without this guard every call would raise
    // a new objection and spawn a new monitor task.
    if (mcu_halt_monitor_started) return;
    mcu_halt_monitor_started = 1'b1;
    phase.raise_objection(this, "MCU halt monitor: waiting for MCU to halt");
    `uvm_info("phase_ready_to_end",
        $sformatf("MCU halt objection raised. Timeout = %0t.", get_mcu_halt_timeout()),
        UVM_LOW)
    fork
        mcu_halt_monitor_task(phase);
    join_none
endfunction

// -----------------------------------------------------------------------------
// mcu_halt_monitor_task: waits for bfm_if.mcu_halt_status to assert (meaning
// the MCU firmware called csr_write_mpmc_halt()) then drops the run_phase
// objection. A timeout guard issues a UVM_ERROR and drops the objection so
// the simulation does not hang.
// -----------------------------------------------------------------------------
task caliptra_ss_usb_base_test::mcu_halt_monitor_task(uvm_phase phase);
    automatic time mcu_timeout = get_mcu_halt_timeout();
    automatic time start_time  = $time;

    `uvm_info("phase_ready_to_end",
        $sformatf("MCU halt monitor started (timeout = %0t, started at %0t).",
                  mcu_timeout, start_time),
        UVM_LOW)

    fork
        begin : WAIT_MCU_HALT
            // bfm_if.mcu_halt_status mirrors cptra_ss_mcu_halt_status_o from
            // caliptra_ss_top_tb via an assign in the TB top. 
            // Level check first: if the signal is already high when the monitor
            // starts (MCU halted before phase_ready_to_end was called), a plain
            // @(posedge ...) would miss it and wait forever. The guard below
            // proceeds immediately in that case.
            if (!bfm_if.mcu_halt_status) begin
                `uvm_info("phase_ready_to_end", "Waiting for posedge of mcu_hal_status", UVM_LOW)
                @(posedge bfm_if.mcu_halt_status);
            end
            begin
                string msg;
                msg = $sformatf("MCU halt detected at %0t (elapsed %0t). Dropping run_phase objection.", $time, $time - start_time);
                `uvm_info("phase_ready_to_end", msg, UVM_LOW)
            end
            #10ns;
            disable TIMEOUT_GUARD;
        end
        begin : TIMEOUT_GUARD
            #(mcu_timeout);
            begin
                string emsg;
                emsg = $sformatf("TIMEOUT: MCU did not halt within %0t (started at %0t). Possible outstanding AXI transactions from MCU. Dropping objection to avoid simulation hang. Override get_mcu_halt_timeout() in the derived test if this test legitimately needs more time.", mcu_timeout, start_time);
                `uvm_error("phase_ready_to_end", emsg)
            end
            disable WAIT_MCU_HALT;
        end
    join_any

    phase.drop_objection(this, "MCU halt detected (or timeout expired)");
endtask

// -----------------------------------------------------------------------------
function void caliptra_ss_usb_base_test::final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...", UVM_LOW)
    super.final_phase(phase);

    svr = uvm_report_server::get_server();
    if (svr.get_severity_count(UVM_FATAL) +
      svr.get_severity_count(UVM_ERROR) > 0)
      begin
        `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_LOW)
        $display("* TESTCASE FAILED");
      end
    else
      begin
        `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_LOW)
        $display("* TESTCASE PASSED");
      end

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
endfunction

`endif // CALIPTRA_SS_USB_BASE_TEST_SV
