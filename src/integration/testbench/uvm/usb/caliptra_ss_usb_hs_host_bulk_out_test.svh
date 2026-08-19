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

`ifndef CALIPTRA_SS_USB_HS_HOST_BULK_OUT_TEST_SV
`define CALIPTRA_SS_USB_HS_HOST_BULK_OUT_TEST_SV

// =============================================================================
// USB High-Speed host bulk OUT test  --  DUT is HOST, VIP is DEVICE.
//
// This test exercises the USBHSH (ip_3515 ATL host controller) inside the
// Caliptra SS DUT.  The MCU firmware (caliptra_ss_usb_hs_host_bulk_out.c):
//   - Asserts HCRESET, clears PORTMODE[16] for HOST mode.
//   - Sets RS, PP, PR (no PFSC -- HS capable).
//   - Waits for HS chirp negotiation (PSPD=HS), then writes ATL PTD for a
//     7KB BULK OUT to device_address=1, EP1.
//   - Polls ATL_IRQ and checks NrBytesTransfered=7168.
//
// VIP topology (SVT b2b_phy example: ts.basic_additional_20_utmi_host_phy_device_mac):
//   Single DEVICE/SERIAL_IF HS agent connected to nvs_usb_phy DP/DM serial bus.
//   nvs_usb_phy bridges DUT HOST MAC UTMI signals to/from the DP/DM serial bus.
//
//   Configuration follows SVT example env/usb_shared_cfg.sv (b2b_phy):
//     dummy_host_cfg  (HOST/TLM): cross-reference holder only, no interface.
//     dev_agent_cfg   (DEVICE/SERIAL_IF/HS): installs as cfg.host_cfg.
//       - Autonomously detects SE0 on DP/DM bus, fires chirp-K after tdrst
//       - device_address=1, EP1=BULK OUT HS 512-byte
//
//   The env build_phase already checks: if (cfg.host_cfg.component_type==DEVICE)
//   it skips the remote_cfg clone entirely.  The single agent acts as
//   the HS DEVICE on the serial DP/DM bus.
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_host_bulk_out_test
// =============================================================================
class caliptra_ss_usb_hs_host_bulk_out_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_host_bulk_out_test)

    function new(string name = "caliptra_ss_usb_hs_host_bulk_out_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        // Dummy HOST cfg needed for VIP cross-reference (SVT example pattern).
        svt_usb_agent_configuration dummy_host_cfg;
        // Fresh DEVICE/UTMI_IF HS cfg installed as cfg.host_cfg.
        svt_usb_agent_configuration dev_agent_cfg;

        `uvm_info("build_phase", "Entered...", UVM_LOW)

        // super.build_phase() calls setup_usb_20_utmi_host_defaults() and
        // creates the env.  We replace cfg.host_cfg after this call.
        super.build_phase(phase);

        // ------------------------------------------------------------------
        // Build dummy_host_cfg: minimal HOST/TLM object for cross-reference.
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
        // Timer values match dev_agent_cfg below.
        dummy_host_cfg.tsigatt     = 100_000_000.0;     // 100 us in ps
        dummy_host_cfg.tdrst       = 1_500_000_000.0;   // 1.5 ms in ps
        dummy_host_cfg.tddis       = 5_000_000_000.0;   // 5 ms in ps
        dummy_host_cfg.tinactivity = 5_000_000_000.0;   // 5 ms in ps

        // ------------------------------------------------------------------
        // Build dev_agent_cfg: DEVICE/UTMI_IF HS agent for the UTMI bus.
        //
        // Cross-reference pattern from SVT b2b_phy example:
        //   dev_agent_cfg.remote_host_cfg    = dummy_host_cfg.local_host_cfg
        //   dev_agent_cfg.remote_device_cfg_size = 0
        //   dummy_host_cfg.remote_device_cfg = dev_agent_cfg.local_device_cfg
        // ------------------------------------------------------------------
        dev_agent_cfg = new("dev_agent_cfg");
        dev_agent_cfg.component_type          = svt_usb_types::DEVICE;
        dev_agent_cfg.top_layer               = svt_usb_agent_configuration::PROTOCOL;

        // DEVICE on USB_20_SERIAL_IF -- connects to DUT HOST via nvs_usb_phy DP/DM bus.
        // The serial interface topology requires nvs_usb_phy to translate between
        // the DUT HOST MAC UTMI signals and the DP/DM serial bus.
        dev_agent_cfg.usb_20_signal_interface = svt_usb_configuration::USB_20_SERIAL_IF;
        dev_agent_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
        dev_agent_cfg.usb_capability          = svt_usb_configuration::USB_20_ONLY;
        dev_agent_cfg.capability              = svt_usb_configuration::PLAIN;
        dev_agent_cfg.speed                   = svt_usb_types::HS;

        // DEVICE has no local host stack.
        dev_agent_cfg.local_host_cfg = null;

        // Cross-references (SVT b2b_phy pattern).
        dev_agent_cfg.remote_host_cfg        = dummy_host_cfg.local_host_cfg;
        dev_agent_cfg.remote_device_cfg_size = 0;

        // Auto-attach at 10 us (before DUT sets PP+PR at ~44 us).
        dev_agent_cfg.poweron_auto_attach_delay = 10_000_000.0; // 10 us in ps

        // One device configuration entry.
        dev_agent_cfg.local_device_cfg_size = 1;
        dev_agent_cfg.local_device_cfg[0]   = new();

        // Device address 1 (matches PTD W1 DevAddr field -- no enumeration).
        dev_agent_cfg.local_device_cfg[0].device_address               = 7'd1;
        dev_agent_cfg.local_device_cfg[0].connected_hub_device_address = 7'd0;

        // HS capable. high_speed_capable=1 keeps the VIP in PERIPHERAL_HI_SPEED
        // after BUS_RESET exit (default 0 causes fallback to PERIPHERAL_FULL_SPEED,
        // making the VIP unable to decode HS OUT tokens from the ATL).
        dev_agent_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::HS;
        dev_agent_cfg.local_device_cfg[0].functionality_support = svt_usb_types::HS;
        dev_agent_cfg.local_device_cfg[0].high_speed_capable    = 1'b1;

        // EP0 CONTROL + EP1 BULK OUT.
        dev_agent_cfg.local_device_cfg[0].num_endpoints = 2;

        // 10 ms timeout: ATL starts at ~4 ms after boot.
        dev_agent_cfg.local_device_cfg[0].device_timeout = 10_000_000_000.0; // 10 ms in ps

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

        // EP1: BULK OUT, HS 512-byte (DUT HOST sends, VIP DEVICE receives).
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1]                 = new();
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::OUT;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size  = 0;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size =
            `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].speed = svt_usb_types::HS;

        // Complete dummy_host_cfg cross-references.
        dummy_host_cfg.remote_device_cfg_size = dev_agent_cfg.local_device_cfg_size;
        dummy_host_cfg.remote_device_cfg      = dev_agent_cfg.local_device_cfg;
        dummy_host_cfg.remote_host_cfg        = dev_agent_cfg.local_host_cfg; // null

        // Apply VIP scaledown timer preset, then override critical timers.
        void'(dev_agent_cfg.set_timer_values(
            svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));

        // tsigatt: debounce after J-state / D+ pull-up detected.
        dev_agent_cfg.tsigatt = 100_000_000.0;  // 100 us in ps

        // tdrst: time DEVICE waits after detecting SE0 before firing chirp-K.
        // Timeline:
        //   t=10 us   : VIP attaches (J-state)
        //   t=~44 us  : DUT sets PP+PR, SE0 starts
        //   t=~144 us : tsigatt expires, tdrst timer starts
        //   t=144+50 = 194 us : DEVICE fires chirp-K
        //   t=~1371 us: DUT clears PR (SE0 ends)
        //   HS chirp K-J-K-J-K-J completes during 194-1371 us window.
        dev_agent_cfg.tdrst = 50_000_000.0;     // 50 us in ps

        // twtrev: time DEVICE waits after RECEIVING_IS for a SOF/token before
        // re-entering BUS_RESET.  The DUT issues its first SOF ~125 us after
        // ATL_EN fires.  ATL_EN fires a few hundred ns before the default
        // twtrev=301 us window closes, which is not enough margin.  Set to
        // 10 ms so the DUT has ample time to issue the first HS SOF frame.
        dev_agent_cfg.twtrev = 10_000_000_000.0; // 10 ms in ps

        // tddis: must exceed HS SOF period.  5 ms prevents DISCONNECTED during
        // inter-SOF idle while ATL is preparing transfers.
        dev_agent_cfg.tddis = 5_000_000_000.0;  // 5 ms in ps (longint repr)

        // tinactivity: prevent SUSPENDED before ATL sends first tokens (~4 ms).
        dev_agent_cfg.tinactivity = 5_000_000_000.0; // 5 ms in ps

        // Tracing flags.
        dev_agent_cfg.enable_prot_tracing            = 1;
        dev_agent_cfg.enable_link_tracing            = 1;
        dev_agent_cfg.enable_phys_tracing            = 1;
        dev_agent_cfg.enable_phys_reporting          = 1;
        dev_agent_cfg.enable_runtime_trace_recording = 1;

        // Install as host_cfg.  The env build_phase sees component_type==DEVICE
        // and skips the remote_cfg clone, leaving the single agent as DEVICE.
        cfg.host_cfg = dev_agent_cfg;

        `uvm_info("build_phase",
            "dev_agent_cfg (DEVICE/SERIAL_IF/HS): addr=1, EP1=BULK OUT, tdrst=50us, attach=10us",
            UVM_LOW)
        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // start_of_simulation_phase: dump full VIP device agent configuration.
    //
    // Printed once after elaboration so the full config is visible at the top
    // of the simulation log for offline analysis.
    // -------------------------------------------------------------------------
    virtual function void start_of_simulation_phase(uvm_phase phase);
        svt_usb_agent_configuration  dcfg;
        svt_usb_device_configuration devcfg;
        int unsigned                 ep;

        super.start_of_simulation_phase(phase);

        if (!$cast(dcfg, cfg.host_cfg)) begin
            `uvm_warning("VIP_CFG_DUMP", "Cannot cast cfg.host_cfg to svt_usb_agent_configuration - skip dump")
            return;
        end

        `uvm_info("VIP_CFG_DUMP", "======= VIP device agent configuration dump =======", UVM_LOW)

        // --- Agent-level fields ---
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  component_type          = %s",
            dcfg.component_type.name()), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  usb_20_signal_interface = %s",
            dcfg.usb_20_signal_interface.name()), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  usb_capability          = %s",
            dcfg.usb_capability.name()), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  speed                   = %s",
            dcfg.speed.name()), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  top_layer               = %s",
            dcfg.top_layer.name()), UVM_LOW)

        // --- Timer fields (all in ps) ---
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
            "  tddis                   = %.0f ps  (%.1f ms)",
            dcfg.tddis, dcfg.tddis/1.0e9), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  tinactivity             = %.0f ps  (%.1f ms)",
            dcfg.tinactivity, dcfg.tinactivity/1.0e9), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  poweron_auto_attach_delay = %.0f ps  (%.1f us)",
            dcfg.poweron_auto_attach_delay, dcfg.poweron_auto_attach_delay/1.0e6), UVM_LOW)

        // --- Tracing flags ---
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_prot_tracing            = %0b", dcfg.enable_prot_tracing), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_link_tracing            = %0b", dcfg.enable_link_tracing), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_phys_tracing            = %0b", dcfg.enable_phys_tracing), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_phys_reporting          = %0b", dcfg.enable_phys_reporting), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_runtime_trace_recording = %0b", dcfg.enable_runtime_trace_recording), UVM_LOW)

        // --- local_device_cfg entries ---
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  local_device_cfg_size   = %0d", dcfg.local_device_cfg_size), UVM_LOW)

        for (int i = 0; i < int'(dcfg.local_device_cfg_size); i++) begin
            if (dcfg.local_device_cfg[i] == null) begin
                `uvm_info("VIP_CFG_DUMP",
                    $sformatf("  local_device_cfg[%0d]    = null", i), UVM_LOW)
                continue;
            end
            devcfg = dcfg.local_device_cfg[i];
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].device_address         = %0d", i, devcfg.device_address), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].connected_bus_speed    = %s", i, devcfg.connected_bus_speed.name()), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].functionality_support  = %s", i, devcfg.functionality_support.name()), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].high_speed_capable     = %0b", i, devcfg.high_speed_capable), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].num_endpoints          = %0d", i, devcfg.num_endpoints), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].device_timeout         = %.0f ps  (%.1f ms)",
                i, devcfg.device_timeout, devcfg.device_timeout/1.0e9), UVM_LOW)

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

        `uvm_info("VIP_CFG_DUMP", "======= end VIP device agent configuration dump =======", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // run_phase: start the device sequence explicitly.
    // -------------------------------------------------------------------------
    virtual task run_phase(uvm_phase phase);
        caliptra_ss_usb_hs_host_bulk_out_sequence seq;

        phase.raise_objection(this, "USB HS host bulk OUT sequence running");

        `uvm_info("run_phase",
            "Starting caliptra_ss_usb_hs_host_bulk_out_sequence on host_agent.virt_sequencer",
            UVM_LOW)

        seq = caliptra_ss_usb_hs_host_bulk_out_sequence::type_id::create("seq");
        seq.start(env.host_agent.virt_sequencer);

        `uvm_info("run_phase",
            "caliptra_ss_usb_hs_host_bulk_out_sequence completed.", UVM_LOW)

        phase.drop_objection(this, "USB HS host bulk OUT sequence done");
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_BULK_OUT_TEST_SV
