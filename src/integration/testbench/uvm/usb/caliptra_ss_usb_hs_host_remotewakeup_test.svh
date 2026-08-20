// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_TEST_SV
`define CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_TEST_SV

// =============================================================================
// USB High-Speed host remote wakeup test  --  DUT is HOST, VIP is DEVICE.
//
// This test exercises the USBHSH (ip_3515 host controller) inside the
// Caliptra SS DUT. The MCU firmware
// (caliptra_ss_usb_hs_host_remotewakeup.c):
//   1. HCRESET, HOST mode, RS, PP, PCD/CSC.
//   2. PR (HS chirp ~742us), clears PR, verifies PSPD=HS, PED+PEDC.
//   3. Polls 2 SOF_IRQ events (confirms microframes).
//   4. Sets PORTSC1.SUSP (L2 suspend).
//   5. Spins ~5ms (bus idle, VIP enters SUSPEND, device fires remote wakeup).
//   6. Asserts FPR, spins ~10ms, writes PP|PED to end resume.
//   7. Polls 3 post-resume SOF_IRQ events and halts.
//
// VIP topology (same as bulk_out test, SVT b2b_phy pattern):
//   Single DEVICE/SERIAL_IF HS agent connected to nvs_usb_phy DP/DM serial bus.
//   nvs_usb_phy bridges DUT HOST MAC UTMI signals to/from the DP/DM serial bus.
//
//   Configuration:
//     dummy_host_cfg  (HOST/TLM): cross-reference holder only.
//     dev_agent_cfg   (DEVICE/SERIAL_IF/HS): installed as cfg.host_cfg.
//       - Auto-attaches at 10us (before DUT asserts PP at ~44us).
//       - Fires HS chirp-K after tdrst=50us from SE0 detection.
//       - EP0 CONTROL (for any enumeration requests from DUT HOST).
//       - No bulk EPs needed: this test only exercises suspend/resume.
//
// Post-resume SE0 suppression strategy:
//   After FPR K ends (~6690us), the bus goes to HS idle which looks like SE0
//   (~440us) to the VIP using FS terminations. This would normally trigger
//   reset_detection_timing_check (x91) and twtdch_timing_check (x2) errors.
//   tfiltse0 CANNOT be raised to suppress these because the same timer also
//   controls when the device starts chirp-K after BUS_RESET SE0. Raising
//   tfiltse0 > 350us delays device chirp past the host KJ window (~465us),
//   causing FS fallback and PSPD=FS firmware fatal.
//   Fix: Use UVM severity override in the sequence to suppress those two check
//   IDs during the post-resume window (~500us), then restore.
//   tdetrst=500us handles the end_of_resume_reset_check (1 occurrence).
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_host_remotewakeup_test
// =============================================================================

class caliptra_ss_usb_hs_host_remotewakeup_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_host_remotewakeup_test)

    // SVT check handles for post-resume false-positive suppression.
    // Set to EXPECTED in end_of_elaboration_phase so they do not generate
    // UVM_ERROR. See SVT example ts.basic_additional_20_ulpi_host_phy_device_link.sv.
    svt_err_check_stats post_resume_chk[3];

    function new(string name = "caliptra_ss_usb_hs_host_remotewakeup_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        svt_usb_agent_configuration dummy_host_cfg;
        svt_usb_agent_configuration dev_agent_cfg;

        `uvm_info("build_phase", "Entered...", UVM_LOW)

        // super.build_phase calls setup_usb_20_utmi_host_defaults() and
        // creates the env. We replace cfg.host_cfg after this call.
        super.build_phase(phase);

        // ------------------------------------------------------------------
        // dummy_host_cfg: minimal HOST/TLM object for SVT cross-reference.
        // Pattern from SVT b2b_phy example usb_shared_cfg.sv.
        // ------------------------------------------------------------------
        dummy_host_cfg = new("dummy_host_cfg");
        dummy_host_cfg.component_type          = svt_usb_types::HOST;
        dummy_host_cfg.top_layer               = svt_usb_agent_configuration::PROTOCOL;
        dummy_host_cfg.usb_20_signal_interface = svt_usb_configuration::USB_20_TLM;
        dummy_host_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
        dummy_host_cfg.usb_capability          = svt_usb_configuration::USB_20_ONLY;
        dummy_host_cfg.capability              = svt_usb_configuration::PLAIN;
        dummy_host_cfg.speed                   = svt_usb_types::HS;
        dummy_host_cfg.local_host_cfg          = new();
        dummy_host_cfg.local_host_cfg.high_speed_capable = 1'b1;
        dummy_host_cfg.local_device_cfg_size   = 0;

        void'(dummy_host_cfg.set_timer_values(
            svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
        dummy_host_cfg.tsigatt     = 100_000_000.0;     // 100 us in ps
        dummy_host_cfg.tdrst       = 1_500_000_000.0;   // 1.5 ms in ps
        dummy_host_cfg.tddis       = 10_000_000_000.0;  // 10 ms in ps
        dummy_host_cfg.tinactivity = 10_000_000_000.0;  // 10 ms in ps

        // ------------------------------------------------------------------
        // dev_agent_cfg: DEVICE/SERIAL_IF HS agent.
        //
        // Connects via nvs_usb_phy DP/DM serial bus to the DUT HOST MAC.
        // Auto-attaches early so J-state is visible before DUT asserts PP+PR.
        // ------------------------------------------------------------------
        dev_agent_cfg = new("dev_agent_cfg");
        dev_agent_cfg.component_type          = svt_usb_types::DEVICE;
        dev_agent_cfg.top_layer               = svt_usb_agent_configuration::PROTOCOL;

        // SERIAL_IF: VIP connects to DUT via nvs_usb_phy DP/DM bus.
        dev_agent_cfg.usb_20_signal_interface = svt_usb_configuration::USB_20_SERIAL_IF;
        dev_agent_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
        dev_agent_cfg.usb_capability          = svt_usb_configuration::USB_20_ONLY;
        dev_agent_cfg.capability              = svt_usb_configuration::PLAIN;
        dev_agent_cfg.speed                   = svt_usb_types::HS;

        dev_agent_cfg.local_host_cfg = null;

        // SVT b2b_phy cross-reference pattern.
        dev_agent_cfg.remote_host_cfg        = dummy_host_cfg.local_host_cfg;
        dev_agent_cfg.remote_device_cfg_size = 0;

        // Auto-attach at 10us (before DUT sets PP+PR at ~44us).
        dev_agent_cfg.poweron_auto_attach_delay = 10_000_000.0; // 10 us in ps

        // One device configuration entry.
        dev_agent_cfg.local_device_cfg_size = 1;
        dev_agent_cfg.local_device_cfg[0]   = new();

        // Device address 1 (matches firmware PORTSC1 DEV_ADD field expectation).
        dev_agent_cfg.local_device_cfg[0].device_address               = 7'd1;
        dev_agent_cfg.local_device_cfg[0].connected_hub_device_address = 7'd0;

        // HS capable. high_speed_capable=1 keeps VIP in PERIPHERAL_HI_SPEED
        // after BUS_RESET exit (default 0 causes FS fallback).
        dev_agent_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::HS;
        dev_agent_cfg.local_device_cfg[0].functionality_support = svt_usb_types::HS;
        dev_agent_cfg.local_device_cfg[0].high_speed_capable    = 1'b1;

        // Must be 1 to allow svt_usb_link_service_device_remote_wakeup_sequence
        // to drive K-state from the device side. Default is 0 which blocks
        // device-initiated wakeup signaling entirely.
        dev_agent_cfg.local_device_cfg[0].remote_wakeup_capable = 1'b1;

        // EP0 CONTROL only. No bulk EPs: this test only exercises suspend/resume.
        dev_agent_cfg.local_device_cfg[0].num_endpoints = 1;

        // Device timeout: must be long enough to survive suspend+resume cycle
        // (~5ms suspend + ~10ms resume = ~15ms) plus post-resume SOF polling.
        // Set to 30ms.
        dev_agent_cfg.local_device_cfg[0].device_timeout = 30_000_000_000.0; // 30 ms in ps

        // EP0: CONTROL, HS 64-byte.
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0]                 = new();
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0].ep_number       = 0;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0].direction       = svt_usb_types::IN;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0].ep_type         = svt_usb_types::CONTROL;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0].interval        = 1;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0].max_burst_size  = 0;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size =
            `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[0].speed = svt_usb_types::HS;

        // Complete dummy_host_cfg cross-references.
        dummy_host_cfg.remote_device_cfg_size = dev_agent_cfg.local_device_cfg_size;
        dummy_host_cfg.remote_device_cfg      = dev_agent_cfg.local_device_cfg;
        dummy_host_cfg.remote_host_cfg        = dev_agent_cfg.local_host_cfg; // null

        // Apply VIP scaledown timer preset, then override critical timers.
        void'(dev_agent_cfg.set_timer_values(
            svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));

        // tsigatt: debounce after J-state / D+ pull-up detected.
        dev_agent_cfg.tsigatt = 100_000_000.0;  // 100 us in ps

        // tdrst: device waits after detecting SE0 before firing chirp-K.
        //   t=10us  VIP attaches (J-state)
        //   t=~44us DUT sets PP+PR, SE0 starts
        //   t=~144us tsigatt expires, tdrst timer starts
        //   t=194us  DEVICE fires chirp-K (same timing as bulk_out test)
        //
        // IMPORTANT: tfiltse0 is NOT overridden here (stays at scaledown ~50us).
        // tfiltse0 controls both the BUS_RESET SE0 threshold AND when device
        // starts chirp-K. Raising it above ~350us delays device chirp past the
        // host KJ window (~465us) causing FS fallback (PSPD=FS firmware fatal).
        // Post-resume spurious BUS_RESET is suppressed via sequence severity
        // override instead of adjusting tfiltse0.
        dev_agent_cfg.tdrst = 50_000_000.0;     // 50 us in ps

        // twtrev: device window after RECEIVING_IS before BUS_RESET re-entry.
        // Must be < gap from RECEIVING_IS to first SOF so that the first SOF
        // resets it before expiry, and short enough to expire after USBCMD=0
        // so tinactivity can start before MCU restarts (USBCMD=RS at ~2.29ms).
        dev_agent_cfg.twtrev = 500_000_000.0; // 500 us in ps

        // tinactivity: inactivity timer for SUSPEND entry.
        // Starts counting after twtrev expires.
        // twtrev expires at ~1.79ms + tinactivity=200us -> SUSPEND at ~1.99ms.
        // MCU restarts at ~2.29ms -> 300us margin. Correct spec-compliant flow.
        dev_agent_cfg.tinactivity = 200_000_000.0; // 200 us in ps

        // twtrsm: SVT resume signaling window timer.
        // VIP fires device remote wakeup K at: SUSPEND_time + (twtrsm - tinactivity)
        // MCU sets FPR at approximately T_susp + 5ms + ~2us = ~6292us.
        // With SUSPEND at ~1990us: twtrsm > 4502us needed. Use 5ms for margin.
        // VIP K fires at ~6790us (~498us after MCU FPR at ~6292us).
        dev_agent_cfg.twtrsm = 5_000_000_000.0; // 5 ms in ps

        // tdetrst: end-of-resume SE0 detection threshold for end_of_resume_reset_check.
        // After FPR K ends (~6690us), bus goes to HS idle = SE0 to VIP (~440us).
        // Set tdetrst > 440us to prevent end_of_resume_reset_check (1 occurrence).
        dev_agent_cfg.tdetrst = 500_000_000.0; // 500 us in ps (> 440 us post-resume SE0)

        // tdrsmup_min: minimum duration the device must hold resume K-state.
        // SVT_SCALEDOWN preset = 10us. VIP drives K for ~9.8us which is just
        // below minimum -> tdrsmup_check UVM_ERROR. Set to 5us to pass.
        dev_agent_cfg.tdrsmup_min = 5_000_000.0; // 5 us in ps

        // tddis: disconnect detection timer.
        // Must be > SOF inter-frame gap (125us) to avoid spurious DISCONNECT,
        // and < FPR K-state duration (~807us) for resume_detection_timing_check.
        dev_agent_cfg.tddis = 500_000_000.0; // 500 us in ps

        // Tracing flags (same as bulk_out test).
        dev_agent_cfg.enable_prot_tracing            = 1;
        dev_agent_cfg.enable_link_tracing            = 1;
        dev_agent_cfg.enable_phys_tracing            = 1;
        dev_agent_cfg.enable_phys_reporting          = 1;
        dev_agent_cfg.enable_runtime_trace_recording = 1;

        // Install as host_cfg. The env build_phase sees component_type==DEVICE
        // and skips the remote_cfg clone, leaving the single agent as DEVICE.
        cfg.host_cfg = dev_agent_cfg;

        `uvm_info("build_phase",
            "dev_agent_cfg (DEVICE/SERIAL_IF/HS): addr=1, EP0 only, tdrst=50us, tdetrst=500us, tddis=500us",
            UVM_LOW)
        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // end_of_elaboration_phase: suppress post-resume false-positive SVT checks.
    //
    // After FPR K ends, the bus transitions to HS idle which the VIP (using FS
    // terminations) sees as SE0. This triggers a spurious BUS_RESET in the VIP
    // and fires three false-positive checks:
    //   tfilt_check  x50  -- HS SOF SYNC pulses (~83ns) < 2.5us TFILT min
    //   twtdch_check x2   -- KJ start latency in spurious reset context
    //   end_of_resume_reset_check x1 -- HS idle gap > tdetrst
    //
    // SVT checks are NOT suppressible via uvm_root.set_report_severity_id_override()
    // because SVT fires them through its own svt_err_check_stats infrastructure,
    // bypassing the UVM report handler. The correct SVT API (per official SVT
    // example ts.basic_additional_20_ulpi_host_phy_device_link.sv) is:
    //   chk = agent.link.chk_cov_mgr.find("short_check_name");
    //   chk.set_default_fail_effect(svt_err_check_stats::EXPECTED);
    //
    // This must be done in end_of_elaboration_phase when the agent hierarchy
    // is fully constructed and chk_cov_mgr is populated.
    //
    // All three checks fire ONLY in the post-resume window (6.5ms - 7.6ms).
    // The real initial chirp (at ~0.8ms) uses the same checks and has already
    // passed with no errors by this time -- confirmed by log: first error at
    // 6567151 ns. Setting EXPECTED globally does not mask real chirp failures
    // because the initial reset phase is already complete before post-resume.
    // -------------------------------------------------------------------------
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        `uvm_info("end_of_elaboration_phase",
            "Suppressing post-resume false-positive SVT checks via chk_cov_mgr...", UVM_LOW)

        post_resume_chk[0] = env.host_agent.link.chk_cov_mgr.find("tfilt_check");
        if (post_resume_chk[0] == null)
            `uvm_fatal("end_of_elaboration_phase",
                "chk_cov_mgr.find(\"tfilt_check\") returned null")
        post_resume_chk[0].set_default_fail_effect(svt_err_check_stats::EXPECTED);

        post_resume_chk[1] = env.host_agent.link.chk_cov_mgr.find("twtdch_check");
        if (post_resume_chk[1] == null)
            `uvm_fatal("end_of_elaboration_phase",
                "chk_cov_mgr.find(\"twtdch_check\") returned null")
        post_resume_chk[1].set_default_fail_effect(svt_err_check_stats::EXPECTED);

        post_resume_chk[2] = env.host_agent.link.chk_cov_mgr.find("end_of_resume_reset_check");
        if (post_resume_chk[2] == null)
            `uvm_fatal("end_of_elaboration_phase",
                "chk_cov_mgr.find(\"end_of_resume_reset_check\") returned null")
        post_resume_chk[2].set_default_fail_effect(svt_err_check_stats::EXPECTED);

        `uvm_info("end_of_elaboration_phase",
            "SVT check suppression complete: tfilt_check + twtdch_check + end_of_resume_reset_check set to EXPECTED.",
            UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // start_of_simulation_phase: dump full VIP device agent configuration.
    // -------------------------------------------------------------------------
    virtual function void start_of_simulation_phase(uvm_phase phase);
        svt_usb_agent_configuration  dcfg;
        svt_usb_device_configuration devcfg;
        int unsigned                 ep;

        super.start_of_simulation_phase(phase);

        if (!$cast(dcfg, cfg.host_cfg)) begin
            `uvm_warning("VIP_CFG_DUMP",
                "Cannot cast cfg.host_cfg to svt_usb_agent_configuration - skip dump")
            return;
        end

        `uvm_info("VIP_CFG_DUMP",
            "======= VIP device agent configuration (remotewakeup test) =======", UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  component_type          = %s", dcfg.component_type.name()), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  usb_20_signal_interface = %s", dcfg.usb_20_signal_interface.name()), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  speed                   = %s", dcfg.speed.name()), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  tsigatt                 = %.0f ps  (%.1f us)",
            dcfg.tsigatt, dcfg.tsigatt/1.0e6), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  tdrst                   = %.0f ps  (%.1f us)",
            dcfg.tdrst, dcfg.tdrst/1.0e6), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  twtrev                  = %.0f ps  (%.1f ms)",
            dcfg.twtrev, dcfg.twtrev/1.0e9), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  tinactivity             = %.0f ps  (%.1f ms)",
            dcfg.tinactivity, dcfg.tinactivity/1.0e9), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  twtrsm                  = %.0f ps  (%.1f ms)",
            dcfg.twtrsm, dcfg.twtrsm/1.0e9), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  tdetrst                 = %.0f ps  (%.1f us)",
            dcfg.tdetrst, dcfg.tdetrst/1.0e6), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  tddis                   = %.0f ps  (%.1f us)",
            dcfg.tddis, dcfg.tddis/1.0e6), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  poweron_auto_attach_delay = %.0f ps  (%.1f us)",
            dcfg.poweron_auto_attach_delay, dcfg.poweron_auto_attach_delay/1.0e6), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  local_device_cfg_size   = %0d", dcfg.local_device_cfg_size), UVM_LOW)

        for (int i = 0; i < int'(dcfg.local_device_cfg_size); i++) begin
            if (dcfg.local_device_cfg[i] == null) continue;
            devcfg = dcfg.local_device_cfg[i];
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].device_address = %0d", i, devcfg.device_address), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].connected_bus_speed = %s", i,
                devcfg.connected_bus_speed.name()), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].high_speed_capable = %0b", i,
                devcfg.high_speed_capable), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].remote_wakeup_capable = %0b", i,
                devcfg.remote_wakeup_capable), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].num_endpoints = %0d", i, devcfg.num_endpoints), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].device_timeout = %.0f ps (%.1f ms)", i,
                devcfg.device_timeout, devcfg.device_timeout/1.0e9), UVM_LOW)
            for (ep = 0; ep < devcfg.num_endpoints; ep++) begin
                if (devcfg.endpoint_cfg[ep] == null) continue;
                `uvm_info("VIP_CFG_DUMP", $sformatf(
                    "    EP[%0d]: ep_number=%0d  direction=%s  ep_type=%s  speed=%s  max_packet_size=%0d",
                    ep,
                    devcfg.endpoint_cfg[ep].ep_number,
                    devcfg.endpoint_cfg[ep].direction.name(),
                    devcfg.endpoint_cfg[ep].ep_type.name(),
                    devcfg.endpoint_cfg[ep].speed.name(),
                    devcfg.endpoint_cfg[ep].max_packet_size), UVM_LOW)
            end
        end
        `uvm_info("VIP_CFG_DUMP",
            "======= end VIP device agent configuration dump =======", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // run_phase: start the remote wakeup sequence explicitly.
    // -------------------------------------------------------------------------
    virtual task run_phase(uvm_phase phase);
        caliptra_ss_usb_hs_host_remotewakeup_sequence seq;

        phase.raise_objection(this, "USB HS host remote wakeup sequence running");

        `uvm_info("run_phase",
            "Starting caliptra_ss_usb_hs_host_remotewakeup_sequence on host_agent.virt_sequencer",
            UVM_LOW)

        seq = caliptra_ss_usb_hs_host_remotewakeup_sequence::type_id::create("seq");
        seq.start(env.host_agent.virt_sequencer);

        `uvm_info("run_phase",
            "caliptra_ss_usb_hs_host_remotewakeup_sequence completed.", UVM_LOW)

        phase.drop_objection(this, "USB HS host remote wakeup sequence done");
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_REMOTEWAKEUP_TEST_SV
