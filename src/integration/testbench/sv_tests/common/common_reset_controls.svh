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


class reset_delay;
  rand int delay;
  int min_delay;
  int max_delay;

  constraint c_delay {
    delay >= min_delay;
    delay <= max_delay;
  }

  function new(int min_d, int max_d);
    min_delay = min_d;
    max_delay = max_d;
  endfunction
endclass

semaphore modify_cptra_pwrgood;
semaphore modify_cptra_rst_b;

initial begin
    modify_cptra_pwrgood = new(1);
    modify_cptra_rst_b = new(1);
end

task automatic assert_cptra_pwrgood(int max_delay = 100, int min_delay = 0);

    reset_delay delay_gen = new(min_delay, max_delay);
    
    modify_cptra_pwrgood.get();

    if (!delay_gen.randomize()) begin
        $fatal("Randomization failed!");
    end

    $display("RESET - Caliptra powergood ASSERTION triggered with delay: %0d at time %0t", delay_gen.delay, $time);

    // Delay then assert reset
    repeat (delay_gen.delay) @(posedge core_clk);
    $display("[%t] RESET - Caliptra powergood ASSERTED", $time);
    cptra_pwrgood <= 1'b0;

    modify_cptra_pwrgood.put();
endtask

task automatic deassert_cptra_pwrgood(int max_delay = 100, int min_delay = 0);
    reset_delay delay_gen = new(min_delay, max_delay);
    
    modify_cptra_pwrgood.get();

    if (!delay_gen.randomize()) begin
        $fatal("Randomization failed!");
    end

    $display("RESET - Caliptra powergood DEASSERTION triggered with delay: %0d at time %0t", delay_gen.delay, $time);

    // Delay then assert reset
    repeat (delay_gen.delay) @(posedge core_clk);
    $display("[%t] RESET - Caliptra powergood DEASSERTED", $time);
    cptra_pwrgood <= 1'b1;

    modify_cptra_pwrgood.put();
endtask

task automatic wait_cptra_pwrgood_deassert();
    @(negedge cptra_pwrgood);
endtask

task automatic wait_cptra_pwrgood_assert();
    @(posedge cptra_pwrgood);
endtask

task automatic assert_cptra_rst_b(int max_delay = 100, int min_delay = 0);
    reset_delay delay_gen = new(min_delay, max_delay);
    
    modify_cptra_rst_b.get();

    if (!delay_gen.randomize()) begin
        $fatal("Randomization failed!");
    end

    $display("RESET - Caliptra reset ASSERTION triggered with delay: %0d at time %0t", delay_gen.delay, $time);

    // Delay then assert reset
    repeat (delay_gen.delay) @(posedge core_clk);
    $display("[%t] RESET - Caliptra reset ASSERTED", $time);
    cptra_rst_b <= 1'b0;

    modify_cptra_rst_b.put();
endtask

task automatic deassert_cptra_rst_b(int max_delay = 100, int min_delay = 0);
    reset_delay delay_gen = new(min_delay, max_delay);
    
    modify_cptra_rst_b.get();

    if (!delay_gen.randomize()) begin
        $fatal("Randomization failed!");
    end

    $display("RESET - Caliptra reset DEASSERTION triggered with delay: %0d at time %0t", delay_gen.delay, $time);

    // Delay then assert reset
    repeat (delay_gen.delay) @(posedge core_clk);
    $display("[%t] RESET - Caliptra reset DEASSERTED", $time);
    cptra_rst_b <= 1'b1;

    modify_cptra_rst_b.put();
endtask

task automatic wait_mci_rst_b_deassert();
    $display("[%t] Waiting for MCI reset deassertion", $time);
    wait(`MCI_PATH.cptra_ss_rst_b_o);
    $display("%t] MCI reset deasserted", $time);
endtask

task automatic wait_mci_rst_b_assert();
    $display("[%t] Waiting for MCI reset assertion", $time);
    wait(!`MCI_PATH.cptra_ss_rst_b_o);
    $display("%t] MCI reset asserted", $time);
endtask

task automatic wait_mcu_rst_b_deassert();
    $display("[%t] Waiting for MCU reset deassertion", $time);
    wait(`MCU_PATH.rst_l);
    $display("%t] MCU reset deasserted", $time);
endtask

task automatic wait_mcu_rst_b_assert();
    $display("[%t] Waiting for MCU reset assertion", $time);
    wait(!`MCU_PATH.rst_l);
    $display("%t] MCU reset asserted", $time);
endtask

task automatic halt_mcu_core(int max_delay = 100, int min_delay = 0);
    reset_delay delay_gen = new(min_delay, max_delay);

    if (!delay_gen.randomize()) begin
        $fatal("Randomization failed!");
    end

    $display("Halting MCU with delay: %0d at time %0t", delay_gen.delay, $time);
    repeat (delay_gen.delay) @(posedge core_clk);

    force `MCI_PATH.mcu_cpu_halt_req_o = 1;
    $display("Waiting for MCU to halt at time %0t", $time);
    while(!`MCI_PATH.mcu_cpu_halt_ack_i)
        @(posedge core_clk);
    $display("Received ack = %0d, Waiting for MCU halt status at time %0t", `MCI_PATH.mcu_cpu_halt_ack_i, $time);
    
    while(!`MCI_PATH.mcu_cpu_halt_status_i)
        @(posedge core_clk);
    $display("Received halt status = %0d, releasing halt req at time %0t", `MCI_PATH.mcu_cpu_halt_status_i, $time);

    release `MCI_PATH.mcu_cpu_halt_req_o;

endtask
