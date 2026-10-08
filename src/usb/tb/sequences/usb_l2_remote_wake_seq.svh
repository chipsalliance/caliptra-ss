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

// Requests remote wake from L2 and verifies the USB 2.0 resume timeline.
class usb_l2_remote_wake_seq extends usb_resume_recovery_seq;
  `uvm_object_utils(usb_l2_remote_wake_seq)

  localparam time HS_RESTORE_LIMIT = 1333333ps;

  time suspend_timeout = 35ms;
  time remote_wake_idle_time = 5ms;
  time device_k_minimum = 1ms;
  time device_k_maximum = 15ms;
  time sof_recovery_timeout = 3ms;
  time software_recovery_time = 10ms;
  time recovery_transfer_timeout = 5ms;
  int unsigned minimum_recovery_sofs = 70;
  time status_poll_interval = 500ns;
  bit completed;
  uvm_event resume_k_started_event;

  function new(string name = "usb_l2_remote_wake_seq");
    super.new(name);
  endfunction

  // Check device K duration and HS restoration from the actual K-to-SE0 edge.
  task observe_resume_signaling(output bit observed);
    realtime device_k_start;
    realtime device_k_release;
    realtime host_eop_start;
    realtime hs_restore_deadline;

    observed = 1'b0;
    fork
      begin
        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
          observed = p_sequencer.ctrl_vif.utmi_opmode === 2'b10 &&
                     p_sequencer.ctrl_vif.utmi_xcvrselect === 1'b1 &&
                     p_sequencer.ctrl_vif.utmi_termselect === 1'b1 &&
                     p_sequencer.ctrl_vif.utmi_txvalid === 1'b1 &&
                     p_sequencer.ctrl_vif.utmi_txdata === 8'h00;
        end while (!observed);
        observed = 1'b0;
        device_k_start = $realtime;
        resume_k_started_event.trigger();
        `uvm_info(
          "USB_L2_REMOTE",
          $sformatf("Device started resume K at %0t", device_k_start),
          UVM_LOW
        )
        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
          if (p_sequencer.ctrl_vif.utmi_txvalid === 1'b1 &&
              (p_sequencer.ctrl_vif.utmi_opmode !== 2'b10 ||
               p_sequencer.ctrl_vif.utmi_xcvrselect !== 1'b1 ||
               p_sequencer.ctrl_vif.utmi_termselect !== 1'b1 ||
               p_sequencer.ctrl_vif.utmi_txdata !== 8'h00)) begin
            `uvm_fatal(
              "USB_L2_REMOTE",
              "Device resume K controls changed before release"
            )
          end
        end while (p_sequencer.ctrl_vif.utmi_txvalid !== 1'b0);
        device_k_release = $realtime;
        if (device_k_release - device_k_start < device_k_minimum ||
            device_k_release - device_k_start > device_k_maximum) begin
          `uvm_fatal(
            "USB_L2_REMOTE",
            $sformatf(
              "Device resume K duration %0t is outside [%0t, %0t]",
              device_k_release - device_k_start,
              device_k_minimum,
              device_k_maximum
            )
          )
        end
        `uvm_info(
          "USB_L2_REMOTE",
          $sformatf(
            "Device released resume K after %0t; host rebroadcast remains active",
            device_k_release - device_k_start
          ),
          UVM_LOW
        )
        p_sequencer.packet_monitor.start_window("Post-L2 remote-wake SOF");

        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
        end while (p_sequencer.ctrl_vif.utmi_linestate !== 2'b10);
        do begin
          @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
        end while (p_sequencer.ctrl_vif.utmi_linestate === 2'b10);
        if (p_sequencer.ctrl_vif.utmi_linestate !== 2'b00) begin
          `uvm_fatal(
            "USB_L2_REMOTE",
            $sformatf(
              "Host resume ended with LineState=%0b instead of K-to-SE0",
              p_sequencer.ctrl_vif.utmi_linestate
            )
          )
        end
        host_eop_start = $realtime;
        hs_restore_deadline = host_eop_start + HS_RESTORE_LIMIT;
        do begin
          if (p_sequencer.ctrl_vif.utmi_opmode === 2'b00 &&
              p_sequencer.ctrl_vif.utmi_xcvrselect === 1'b0 &&
              p_sequencer.ctrl_vif.utmi_termselect === 1'b0 &&
              p_sequencer.ctrl_vif.utmi_txvalid === 1'b0) begin
            observed = 1'b1;
          end else begin
            @(posedge p_sequencer.usb_20_mac_if.utmi_dut_mac_if.CLK);
          end
        end while (!observed && $realtime <= hs_restore_deadline);
        if (!observed) begin
          `uvm_fatal(
            "USB_L2_REMOTE",
            $sformatf(
              "HS controls were not restored within %0t of K-to-SE0 at %0t",
              HS_RESTORE_LIMIT,
              host_eop_start
            )
          )
        end
        `uvm_info(
          "USB_L2_REMOTE",
          $sformatf(
            "HS controls restored %0t after K-to-SE0",
            $realtime - host_eop_start
          ),
          UVM_LOW
        )
      end
      begin
        #(suspend_timeout);
      end
    join_any
    disable fork;
  endtask

  // Enumerate, enter L2, request remote wake, and prove datapath recovery.
  virtual task body();
    usb_init_seq init_sequence;
    usb_l2_remote_wake_host_seq suspend_host_sequence;
    usb_remote_wake_enable_host_seq wake_enable_sequence;
    usb_endpoint_cfg control_endpoint;
    svt_usb_protocol_service_20_sof_off_sequence sof_off_sequence;
    svt_usb_protocol_service_20_sof_on_sequence sof_on_sequence;
    uvm_event dut_suspend_observed;
    uvm_reg_field device_address_field;
    logic [31:0] device_command_status;
    logic [31:0] device_address_mask;
    logic [6:0] observed_device_address;
    logic [31:0] suspend_mask;
    int unsigned recovery_sof_count;
    bit resume_signaling_observed;
    bit sof_observed;

    completed = 1'b0;
    `uvm_info("USB_L2_REMOTE", "Starting L2 remote-wake scenario; running enumeration first", UVM_LOW)
    init_sequence = usb_init_seq::type_id::create("init_sequence");
    init_sequence.start(m_sequencer, this);
    if (!init_sequence.completed) begin
      `uvm_fatal("USB_L2_REMOTE", "Enumeration did not complete")
    end
    if (p_sequencer.ctrl_vif == null || p_sequencer.usb_20_mac_if == null) begin
      `uvm_fatal("USB_L2_REMOTE", "Remote-wake checking requires the USB control and UTMI interfaces")
    end
    control_endpoint = get_endpoint(0, USB_DIRECTION_OUT);
    wake_enable_sequence =
        usb_remote_wake_enable_host_seq::type_id::create(
            "wake_enable_sequence");
    wake_enable_sequence.control_endpoint = control_endpoint;
    wake_enable_sequence.device_address = p_sequencer.cfg.device_address;
    wake_enable_sequence.link_timeout = p_sequencer.cfg.link_timeout;
    wake_enable_sequence.control_transfer_timeout =
        p_sequencer.cfg.control_transfer_timeout;
    clear_endpoint_interrupt(control_endpoint);
    `uvm_info(
      "USB_L2_REMOTE",
      "Enabling DEVICE_REMOTE_WAKEUP before entering suspend",
      UVM_LOW
    )
    fork
      begin
        wake_enable_sequence.start(p_sequencer.host_sequencer);
        if (!wake_enable_sequence.completed) begin
          `uvm_fatal(
            "USB_L2_REMOTE",
            "SET_FEATURE DEVICE_REMOTE_WAKEUP returned incomplete"
          )
        end
      end
      begin
        init_sequence.service_additional_setup_request(
          p_sequencer.cfg.control_transfer_timeout
        );
      end
    join
    if (!init_sequence.remote_wakeup_enabled) begin
      `uvm_fatal(
        "USB_L2_REMOTE",
        "Firmware did not record DEVICE_REMOTE_WAKEUP authorization"
      )
    end

    suspend_mask = ral_field_mask(p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DSUS);
    device_address_field =
        p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT.DEV_ADDR;
    device_address_mask = ral_field_mask(device_address_field);
    dut_suspend_observed = new("dut_suspend_observed");
    resume_k_started_event = new("resume_k_started_event");
    suspend_host_sequence = usb_l2_remote_wake_host_seq::type_id::create("suspend_host_sequence");
    suspend_host_sequence.dut_suspend_observed = dut_suspend_observed;
    suspend_host_sequence.dut_resume_k_started = resume_k_started_event;
    suspend_host_sequence.link_state_timeout = suspend_timeout;
    resume_signaling_observed = 1'b0;

    fork
      begin
        suspend_host_sequence.start(p_sequencer.host_sequencer);
        if (!suspend_host_sequence.completed) begin
          `uvm_fatal("USB_L2_REMOTE", "Host remote-wake observer returned incomplete")
        end
      end
      begin
        poll_csr_bits(
          "DEVCMDSTAT.DSUS assertion",
          p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
          suspend_mask,
          1'b1,
          suspend_timeout,
          device_command_status,
          status_poll_interval
        );
        `uvm_info("USB_L2_REMOTE", $sformatf("DUT entered L2 suspend: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)
        `uvm_info(
          "USB_L2_REMOTE",
          $sformatf(
            "Waiting %0t of continuous idle before authorized remote wake",
            remote_wake_idle_time
          ),
          UVM_LOW
        )
        #(remote_wake_idle_time);
        dut_suspend_observed.trigger();
        device_command_status &= ~suspend_mask;
        `uvm_info(
          "USB_L2_REMOTE",
          "Firmware authorizes remote wake and writes DSUS=0",
          UVM_LOW
        )
        ral_write32("DEVCMDSTAT", p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT, device_command_status);
        poll_csr_bits(
          "DEVCMDSTAT.DSUS deassertion",
          p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
          suspend_mask,
          1'b0,
          suspend_timeout,
          device_command_status,
          status_poll_interval
        );
      end
      begin
        observe_resume_signaling(resume_signaling_observed);
      end
    join
    if (!resume_signaling_observed) begin
      `uvm_fatal("USB_L2_REMOTE", $sformatf("Device resume signaling did not complete within %0t", suspend_timeout))
    end
    p_sequencer.packet_monitor.wait_for_sof(
      sof_recovery_timeout,
      sof_observed
    );
    if (!sof_observed) begin
      `uvm_fatal(
        "USB_L2_REMOTE",
        $sformatf(
          "No host SOF was observed within %0t after resume idle",
          sof_recovery_timeout
        )
      )
    end
    ral_read32(
      "DEVCMDSTAT",
      p_sequencer.reg_model.combo.dev0_csr.DEVCMDSTAT,
      device_command_status
    );
    observed_device_address = 7'(
        (device_command_status & device_address_mask) >>
        device_address_field.get_lsb_pos());
    if (observed_device_address !== p_sequencer.cfg.device_address) begin
      `uvm_fatal(
        "USB_L2_REMOTE",
        $sformatf(
          "Device address changed across resume: observed=%0d expected=%0d",
          observed_device_address,
          p_sequencer.cfg.device_address
        )
      )
    end
    `uvm_info(
      "USB_L2_REMOTE",
      $sformatf(
        "Observed host SOF; waiting %0t software recovery before traffic",
        software_recovery_time
      ),
      UVM_LOW
    )
    #(software_recovery_time);
    recovery_sof_count = p_sequencer.packet_monitor.count_pid(
      svt_usb_packet::SOF,
      usb_packet_monitor_callback::USB_PACKET_TX
    );
    p_sequencer.packet_monitor.stop_window();
    if (recovery_sof_count < minimum_recovery_sofs) begin
      `uvm_fatal(
        "USB_L2_REMOTE",
        $sformatf(
          "Host produced only %0d SOFs during the %0t recovery, expected at least %0d",
          recovery_sof_count,
          software_recovery_time,
          minimum_recovery_sofs
        )
      )
    end
    `uvm_info(
      "USB_L2_REMOTE",
      $sformatf(
        "Observed %0d SOFs during software recovery; switching to controlled UTMI traffic",
        recovery_sof_count
      ),
      UVM_LOW
    )
    sof_off_sequence =
        svt_usb_protocol_service_20_sof_off_sequence::type_id::create(
            "recovery_sof_off_sequence");
    sof_off_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);
    p_sequencer.ctrl_vif.raw_utmi_host_mode <= 1'b1;
    recovery_timeout = recovery_transfer_timeout;
    recovery_poll_interval = status_poll_interval;
    run_raw_recovery_transfer("Post-L2 remote-wake bulk OUT");
    p_sequencer.ctrl_vif.raw_utmi_host_mode <= 1'b0;
    sof_on_sequence =
        svt_usb_protocol_service_20_sof_on_sequence::type_id::create(
            "recovery_sof_on_sequence");
    sof_on_sequence.start(
        p_sequencer.host_sequencer.prot_service_sequencer);
    `uvm_info("USB_L2_REMOTE", $sformatf("DUT left L2 after remote wake: DEVCMDSTAT=0x%08h", device_command_status), UVM_LOW)

    completed = 1'b1;
    `uvm_info(
      "USB_L2_REMOTE",
      "L2 remote wake completed with compliant timing, preserved address, SOF, and recovery traffic",
      UVM_LOW
    )
  endtask
endclass
