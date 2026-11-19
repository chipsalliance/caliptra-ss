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

class usb_ocp_mixed_traffic_host_seq extends usb_ocp_base_epn_overlap_host_seq;
  `uvm_object_utils(usb_ocp_mixed_traffic_host_seq)
  bit native_abort_checked[2];

  function new(string name = "usb_ocp_mixed_traffic_host_seq");
    super.new(name);
    both_epn_devices = 1;
    require_replacement = 1;
    zero_prefix_required = 1;
  endfunction

  virtual task ocp_do_check_paused_continuation(svt_usb_transfer tr,
      int phase, int generation, output bit resumed_original);
    svt_usb_protocol_service service;
    svt_usb_device_status device_status;
    svt_usb_endpoint_status endpoint_status;
    usb_ocp_base_service_callback actual;
    usb_ocp_event native_ended;
    usb_ocp_base_control c;
    logic [`SVT_USB_RESULTS_STATUS_SIZE-1:0] allowed_results;
    longint unsigned command_floor;
    realtime abort_accepted_at;
    resumed_original = 0;
    actual = observer.service_callback;
    c = scoreboard.model.control[1];
    if (!(phase inside {0,1}) || !replacing || actual == null ||
        c.generation != generation || c.data.size() != 0 || c.status_acked)
      `uvm_fatal("OCP_MIXED_STIMULUS", "Mixed replacement lost its paused pre-DATA original")
    scoreboard.model.mixed_generation[phase] = generation;
    // Publish the wait target before native termination can return the
    // original routed response; only the real standard peer satisfies it.
    peer = null;
    replacement_request = tr;
    actual.ocp_configure_abort_capture(tr.device_address,c.setup);
    command_floor = actual.completed_commands;
    service = svt_usb_protocol_service::type_id::create("mixed_clean_abort");
    start_item(service,-1,p_sequencer.prot_service_sequencer);
    service.cfg = usb_cfg;
    if (!service.randomize() with {
          service_type == svt_usb_protocol_service::CMD;
          protocol_command_type == svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER;
          device_address == local::tr.device_address;
          endpoint_number == 0;
          direction == svt_usb_types::OUT;
          force_immediate_abort == 0;
        }) `uvm_fatal("OCP_MIXED_COMMAND", "Clean abort command randomization failed")
    finish_item(service);
    service.end_event.wait_on();
    wait (actual.completed_commands > command_floor);
    if (actual.completed_commands != command_floor+1 ||
        actual.command !== svt_usb_protocol_service::USB_ABORT_CURRENT_TRANSFER ||
        actual.address !== tr.device_address || actual.endpoint !== 0 ||
        actual.force_immediate_abort !== 0 || !actual.accepted ||
        actual.return_status !== 1)
      `uvm_fatal("OCP_MIXED_COMMAND", "Executed clean abort did not accept the sole original target")
    abort_accepted_at = actual.command_ended_at;
    device_status = shared_status.get_device_status(tr.device_address);
    if (device_status == null)
      `uvm_fatal("OCP_MIXED_COMMAND", "Missing original native device status after abort acceptance")
    endpoint_status = device_status.get_endpoint_status(0,svt_usb_types::OUT,1,svt_usb_types::CONTROL);
    if (endpoint_status == null)
      `uvm_fatal("OCP_MIXED_COMMAND", "Missing original native endpoint status after abort acceptance")
    `uvm_info("OCP_MIXED_NATIVE",$sformatf(
      "phase=%0d generation=%0d clean_abort_accepted_at=%0t state=%s ended_before_resume=%0b",
      phase,generation,abort_accepted_at,endpoint_status.processing_paused.name(),
      actual.mixed_native_abort != null),UVM_LOW)
    // Abort acceptance does not promise terminal completion or clearing
    // pause. Resume only a genuinely paused endpoint, never a blind no-op.
    case (endpoint_status.processing_paused)
      svt_usb_endpoint_status::IS_PAUSED: ocp_do_check_native_processing(tr,0);
      svt_usb_endpoint_status::NOT_PAUSED: begin
        `uvm_info("OCP_MIXED_NATIVE", "Abort left endpoint unpaused; no RESUME transition credited",UVM_LOW)
      end
      default: `uvm_fatal("OCP_MIXED_COMMAND", "Unexpected pending native processing state after clean abort")
    endcase
    actual.ocp_wait_native_abort(native_ended);
    allowed_results = 0;
    allowed_results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] = 1;
    if (!tr.setup_data_bmrequesttype_dir) allowed_results[5] = 1;
    if (!native_ended.native_aborted ||
        native_ended.results[usb_ocp_event::SERVICE_ABORT_RESULT_BIT] !== 1 ||
        (native_ended.results & ~allowed_results) !== 0 ||
        native_ended.completed_bytes != 0 || c.data.size() != 0 ||
        !c.active || c.status_acked || c.generation != generation ||
        endpoint_status.processing_paused !== svt_usb_endpoint_status::NOT_PAUSED)
      `uvm_fatal("OCP_MIXED_STIMULUS", "Original did not end ABORTED before old DATA/STATUS progression")
    native_abort_checked[phase] = 1;
    `uvm_info("OCP_MIXED_NATIVE",$sformatf(
      "phase=%0d original_ABORTED_at=%0t results=%0h native_bytes=%0d; submit real replacement SETUP",
      phase,native_ended.observed_at,native_ended.results,native_ended.completed_bytes),UVM_LOW)
    // USB 2.0 5.5.5: only a new ACK-qualified SETUP supersedes DUT control.
    // The checked zero prefix permits a fresh OCP request, not FIFO rollback.
    ocp_do_check_standard_replacement(tr);
  endtask

  task body();
    recovery_status_timeout = 5ms;
    super.body();
    foreach (native_abort_checked[phase])
      if (!native_abort_checked[phase])
        `uvm_fatal("OCP_MIXED_INCOMPLETE", "An original mixed window lacks native abort proof")
    if (!replacement_read_started || !replacement_write_started ||
        peer == null || !peer.completed ||
        observer.service_callback.capture_mixed_abort ||
        observer.service_callback.mixed_native_abort != null)
      `uvm_fatal("OCP_MIXED_INCOMPLETE", "Mixed replacement or native callback work is outstanding")
  endtask
endclass
