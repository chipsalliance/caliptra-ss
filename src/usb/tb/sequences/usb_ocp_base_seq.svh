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

class usb_ocp_base_seq extends usb_base_seq;
  `uvm_object_utils(usb_ocp_base_seq)
  usb_ocp_base_env_cfg ocp_cfg;
  bit completed;

  function new(string name = "usb_ocp_base_seq");
    super.new(name);
  endfunction

  virtual task pre_start();
    super.pre_start();
    if (!$cast(ocp_cfg, p_sequencer.cfg))
      `uvm_fatal("OCP_SEQUENCE", "OCP sequence requires OCP environment configuration")
    if (ocp_cfg.service_poll == 0 || ocp_cfg.idle_poll_max < ocp_cfg.service_poll ||
        ocp_cfg.idle_poll_max > 1ms)
      `uvm_fatal("OCP_SEQUENCE", "OCP polling requires 0 < service_poll <= idle_poll_max <= 1ms")
  endtask

  function time ocp_get_next_idle_poll(time interval);
    if (interval >= ocp_cfg.idle_poll_max/2) return ocp_cfg.idle_poll_max;
    return interval*2;
  endfunction

  // No host protocol state is consulted. Wake only for the elapsed interval,
  // the existing absolute deadline, or explicit lifecycle teardown. Isolate
  // cancellation so it cannot kill any actor or in-flight AXI access.
  task ocp_wait_service_interval(time interval, time deadline,
                                 string report_id, string timeout_message);
    time wait_time;
    if (ocp_cfg.stop_requested === 1'b1) return;
    if ($time >= deadline) `uvm_fatal(report_id,timeout_message)
    wait_time = interval;
    if (wait_time > deadline-$time) wait_time = deadline-$time;
    fork
      begin
        fork
          begin #(wait_time); end
          begin wait (ocp_cfg.stop_requested === 1'b1); end
        join_any
        disable fork;
      end
    join
    if (ocp_cfg.stop_requested !== 1'b1 && $time >= deadline)
      `uvm_fatal(report_id,timeout_message)
  endtask

  task ocp_poll_teardown();
    bit stopped;
    stopped = 0;
    fork
      begin
        fork
          begin wait (ocp_cfg.stop_requested === 1'b1); stopped = 1; end
          begin #(ocp_cfg.actor_timeout); end
        join_any
        disable fork;
      end
    join
    if (!stopped) `uvm_fatal("OCP_TEARDOWN", "Explicit teardown was not requested")
  endtask
endclass
