// SPDX-License-Identifier: Apache-2.0

// Composes the native L1/L2 services from origin/willoneill-usb-l1-host-resume.
// L1 native entry/origin observation follows the reviewed backup correction.
class usb_host_resume_host_seq extends usb_host_base_seq;
  `uvm_object_utils(usb_host_resume_host_seq)

  bit l1 = 1'b1;
  bit [6:0] device_address = USB_DEFAULT_DEVICE_ADDRESS;
  bit [3:0] lpm_hird = 4'h1;
  uvm_event dut_suspended;
  uvm_event host_ready;
  uvm_event recovery_complete;
  bit guard_fs_l2;
  virtual usb_tb_ctrl_if #(
    .UW(usb_tb_pkg::USB_TB_AXI_USER_WIDTH),
    .COMBO_NUM_USERS(usb_tb_pkg::USB_COMBO_NUM_PRIV_AXI_USERS),
    .DEV1_NUM_USERS(usb_tb_pkg::USB_DEV1_NUM_PRIV_AXI_USERS)
  ) ctrl_vif;
  time link_state_timeout = 750us;
  // A full FS frame plus one native service index, not a cadence checker.
  time sof_progress_timeout = 1125us;

  // Construct shared native host-resume stimulus.
  function new(string name = "usb_host_resume_host_seq");
    super.new(name);
  endfunction

  // Use one stable ID across both native power-state paths.
  virtual function string report_id();
    return "USB_HOST_RESUME_HOST";
  endfunction

  // Prearm native entry/origin observation, then request host-owned resume.
  virtual task body();
    svt_usb_protocol_service_usb_20_lpm_sequence lpm_sequence;
    svt_usb_link_service_clear_l1suspend_sequence l1_resume;
    svt_usb_protocol_service_20_sof_off_sequence sof_off;
    svt_usb_protocol_service_20_sof_on_sequence sof_on;
    svt_usb_link_service_clear_suspend_sequence l2_resume;
    process entry_observer;
    process origin_observer;
    process sof_observer;
    process sof_watchdog;
    process watchdog;
    bit entered;
    bit requested;
    bit host_origin;
    bit resume_returned;
    int unsigned post_resume_sofs;
    time scaled_recovery;

    completed = 1'b0;
    entered = 1'b0;
    requested = 1'b0;
    host_origin = 1'b0;
    resume_returned = 1'b0;
    post_resume_sofs = 0;
    resolve_host_context(1'b1);
    if (dut_suspended == null || host_ready == null || recovery_complete == null || host_agent.link == null) begin
      `uvm_fatal(report_id(), "DUT/recovery coordination and native link observation are required")
    end
    if (guard_fs_l2) begin
      real budget_ps;
      budget_ps = usb_vip_cfg_builder::vip_ps(usb_l2_remote_wake_host_seq::ACCELERATED_HOST_RESUME_BUDGET);
      if (l1 || ctrl_vif == null || !(usb_cfg.speed === svt_usb_types::FS) ||
          !((usb_cfg.tdrsmdn == budget_ps) === 1'b1) || !((usb_cfg.tdrsmdn_min == budget_ps) === 1'b1) ||
          !((usb_cfg.tdrsmdn_nom == budget_ps) === 1'b1) ||
          !(usb_cfg.enable_sof_during_recovery === 1'b1) ||
          !((usb_cfg.trsmrcy == usb_vip_cfg_builder::vip_ps(800ns)) === 1'b1)) begin
        `uvm_fatal(report_id(), $sformatf("Invalid guarded FS L2 policy: L1=%b ctrl_vif_present=%b speed=%s downstream_ps=%0.0f/%0.0f/%0.0f integer_ps=%0d/%0d/%0d expected_ps=%0.0f recovery_ps=%0.0f recovery_SOF=%b",
          l1, ctrl_vif != null, usb_cfg.speed.name(), usb_cfg.tdrsmdn, usb_cfg.tdrsmdn_min, usb_cfg.tdrsmdn_nom,
          usb_cfg.tdrsmdn_longint, usb_cfg.tdrsmdn_min_longint, usb_cfg.tdrsmdn_nom_longint, budget_ps,
          usb_cfg.trsmrcy, usb_cfg.enable_sof_during_recovery))
      end
      `uvm_info(report_id(), $sformatf("Guarded functional FS profile: downstream=%0.0f ps recovery=%0.0f ps cycle_bound=%0t",
        usb_cfg.tdrsmdn, usb_cfg.trsmrcy, link_state_timeout), UVM_LOW)
    end
    fork
      begin
        entry_observer = process::self();
        if (l1) host_agent.link.NOTIFY_BUS_IS_L1SUSPENDED.wait_trigger();
        else wait (shared_status.link_usb_20_state === svt_usb_types::SUSPENDED);
        entered = 1'b1;
        `uvm_info(report_id(), $sformatf("Native host L%0d entry observed", l1 ? 1 : 2), UVM_LOW)
      end
      begin
        origin_observer = process::self();
        if (l1) begin
          host_agent.link.NOTIFY_L1_EXIT_VIA_HOST_INITIATED_RESUME.wait_trigger();
        end else begin
          host_agent.link.NOTIFY_L2_EXIT_VIA_HOST_INITIATED_RESUME.wait_trigger();
        end
        if (!entered || !requested) `uvm_fatal(report_id(), "Host-origin resume preceded observed entry or the host request")
        host_origin = 1'b1;
        `uvm_info(report_id(), "Native host-origin resume observed; awaiting ENABLED", UVM_LOW)
      end
      begin
        if (guard_fs_l2) begin
          uvm_object observed_object;
          svt_usb_packet packet;
          sof_observer = process::self();
          forever begin
            host_agent.prot.NOTIFY_20_HOST_TX_PACKET.wait_trigger_data(observed_object);
            if (!$cast(packet, observed_object) || packet == null) `uvm_fatal(report_id(), "Native TX notification did not contain a USB packet")
            if (resume_returned && host_origin && shared_status.link_usb_20_state === svt_usb_types::ENABLED &&
                packet.get_pid_name_val() === svt_usb_packet::SOF) begin
              post_resume_sofs++;
              if (post_resume_sofs == 1 || post_resume_sofs % 8 == 0) begin
                `uvm_info(report_id(), $sformatf("Guarded FS host recovery: actual transmitted SOFs=%0d", post_resume_sofs), UVM_LOW)
              end
            end
          end
        end
      end
      begin
        if (guard_fs_l2) begin
          int unsigned previous_count;
          sof_watchdog = process::self();
          // Service return can precede downstream K/EOR completion.
          wait (resume_returned && host_origin && shared_status.link_usb_20_state === svt_usb_types::ENABLED);
          while (!recovery_complete.is_on()) begin
            previous_count = post_resume_sofs;
            #(sof_progress_timeout);
            if (!recovery_complete.is_on() && post_resume_sofs == previous_count) begin
              `uvm_fatal(report_id(), $sformatf("Guarded FS host recovery lost actual SOF progress: count=%0d state=%s",
                post_resume_sofs, shared_status.link_usb_20_state.name()))
            end
          end
        end
      end
      begin
        watchdog = process::self();
        #(link_state_timeout);
        `uvm_fatal(report_id(), $sformatf("L%0d host cycle timed out: entry=%b requested=%b origin=%b returned=%b SOFs=%0d state=%s",
          l1 ? 1 : 2, entered, requested, host_origin, resume_returned, post_resume_sofs, shared_status.link_usb_20_state.name()))
      end
    join_none
    #0;
    `uvm_info(report_id(), $sformatf("Starting native host L%0d entry: address=%0d HIRD=%0d", l1 ? 1 : 2, device_address, lpm_hird), UVM_LOW)
    if (l1) begin
      lpm_sequence = svt_usb_protocol_service_usb_20_lpm_sequence::type_id::create("lpm_sequence");
      lpm_sequence.blinkstate = 4'h1;
      lpm_sequence.dev_address = device_address;
      lpm_sequence.lpm_hird = lpm_hird;
      lpm_sequence.lpm_bremotewake = 1'b1;
      lpm_sequence.start(p_sequencer.prot_service_sequencer);
    end else begin
      sof_off = svt_usb_protocol_service_20_sof_off_sequence::type_id::create("sof_off");
      sof_off.start(p_sequencer.prot_service_sequencer);
    end
    `uvm_info(report_id(), "Entry service returned; waiting for native entry and DUT status", UVM_LOW)
    wait (entered);
    dut_suspended.wait_on();
    if (guard_fs_l2) begin
      `uvm_info(report_id(), "Qualifying actual DUT suspend and native clock quiescence before accelerated host resume", UVM_LOW)
      while (!((shared_status.link_usb_20_state === svt_usb_types::SUSPENDED) &&
               (ctrl_vif.dut_suspendm === 1'b0) &&
               ctrl_vif.utmi_clock_quiet(usb_l2_remote_wake_host_seq::CLOCK_QUIET_OBSERVATION))) begin
        @(posedge ctrl_vif.clk);
      end
      `uvm_info(report_id(), "Actual DUT suspend/native clock quiescence qualified; proceeding with candidate host budget", UVM_LOW)
    end
    `uvm_info(report_id(), "Native entry and DUT status observed; requesting host resume", UVM_LOW)
    requested = 1'b1;
    if (l1) begin
      l1_resume = svt_usb_link_service_clear_l1suspend_sequence::type_id::create("l1_resume");
      l1_resume.start(p_sequencer.link_service_sequencer);
    end else begin
      l2_resume = svt_usb_link_service_clear_suspend_sequence::type_id::create("l2_resume");
      l2_resume.start(p_sequencer.link_service_sequencer);
      resume_returned = 1'b1;
      sof_on = svt_usb_protocol_service_20_sof_on_sequence::type_id::create("sof_on");
      sof_on.start(p_sequencer.prot_service_sequencer);
    end
    wait (host_origin && shared_status.link_usb_20_state === svt_usb_types::ENABLED);
    if (guard_fs_l2) begin
      scaled_recovery = time'(usb_cfg.trsmrcy * 1ps);
      `uvm_info(report_id(), $sformatf("Native host resume returned/ENABLED; recovery wait=%0t (%0.0f ps), SOFs=%0d",
        scaled_recovery, usb_cfg.trsmrcy, post_resume_sofs), UVM_LOW)
      #(scaled_recovery);
      `uvm_info(report_id(), $sformatf("Native recovery wait complete; waiting for two SOFs, observed=%0d", post_resume_sofs), UVM_LOW)
      wait (post_resume_sofs >= 2);
      `uvm_info(report_id(), "Native recovery and two SOFs observed; qualifying actual FS receive readiness", UVM_LOW)
      while (!ctrl_vif.full_speed_receive_ready()) begin
        @(posedge ctrl_vif.clk);
      end
      `uvm_info(report_id(), "Actual FS receive readiness and two native SOFs observed; admitting public CSR/bulk checks", UVM_LOW)
    end
    host_ready.trigger();
    if (guard_fs_l2) begin
      // Keep native SOF observation/watchdog alive through checked bulk recovery.
      recovery_complete.wait_on();
      sof_observer.kill();
      if (sof_watchdog.status() != process::FINISHED) sof_watchdog.kill();
      `uvm_info(report_id(), $sformatf("Guarded FS host resume admitted checked recovery with %0d actual SOFs observed", post_resume_sofs), UVM_LOW)
    end
    if (entry_observer.status() != process::FINISHED) entry_observer.kill();
    if (origin_observer.status() != process::FINISHED) origin_observer.kill();
    watchdog.kill();
    completed = 1'b1;
    `uvm_info(report_id(), $sformatf("L%0d host entry, host-origin resume and ENABLED verified", l1 ? 1 : 2), UVM_LOW)
  endtask
endclass
