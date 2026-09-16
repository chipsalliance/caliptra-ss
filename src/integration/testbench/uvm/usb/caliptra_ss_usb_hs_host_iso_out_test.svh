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

`ifndef CALIPTRA_SS_USB_HS_HOST_ISO_OUT_TEST_SV
`define CALIPTRA_SS_USB_HS_HOST_ISO_OUT_TEST_SV

// =============================================================================
// USB High-Speed host isochronous OUT test  --  DUT is HOST, VIP is DEVICE.
//
// This test exercises the USBHSH (ip_3515 ISO periodic list) inside the
// Caliptra SS DUT.  The MCU firmware (caliptra_ss_usb_hs_host_iso_out.c):
//   - Asserts HCRESET, clears PORTMODE for HOST mode.
//   - Sets RS, PP, PR (HS capable -- no PFSC).
//   - Waits for HS chirp negotiation (PSPD=HS).
//   - Issues SET_CONFIGURATION(1) to addr=1 via ATL CTRL PTD.
//   - Switches to ISO periodic list (ISO_EN), writes ISO PTD slot 0:
//       EPType=ISO, Token=OUT, MaxPkt=1024, NrBytesToTransfer=1024,
//       DataStartAddr=0x400 (1024B payload word[i]=i), uSA=0xFF.
//   - Polls ISO_IRQ and verifies NrBytesTransferred=1024.
//   - Prints "USB HS host ISO OUT - PASSED" on success.
//
// VIP topology (same as bulk OUT test -- SVT b2b_phy SERIAL_IF):
//   Single DEVICE/SERIAL_IF HS agent connected to nvs_usb_phy DP/DM serial bus.
//   nvs_usb_phy bridges DUT HOST MAC UTMI signals to the DP/DM serial bus.
//
//   Configuration:
//     dummy_host_cfg  (HOST/TLM): cross-reference holder only, no interface.
//     dev_agent_cfg   (DEVICE/SERIAL_IF/HS): installs as cfg.host_cfg.
//       - Autonomously detects SE0 on DP/DM bus, fires chirp-K after tdrst
//       - device_address=1, EP0=CONTROL, EP1=ISO OUT HS 1024-byte
//
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_hs_host_iso_out_test
// =============================================================================
class caliptra_ss_usb_hs_host_iso_out_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_hs_host_iso_out_test)

    function new(string name = "caliptra_ss_usb_hs_host_iso_out_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        svt_usb_agent_configuration dummy_host_cfg;
        svt_usb_agent_configuration dev_agent_cfg;

        `uvm_info("build_phase", "Entered...", UVM_LOW)

        // super.build_phase() calls setup_usb_20_utmi_host_defaults() and
        // creates the env.  We replace cfg.host_cfg after this call.
        super.build_phase(phase);

        // ------------------------------------------------------------------
        // Build dummy_host_cfg: minimal HOST/TLM object for cross-reference.
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
        dummy_host_cfg.tddis       = 5_000_000_000.0;   // 5 ms in ps
        dummy_host_cfg.tinactivity = 5_000_000_000.0;   // 5 ms in ps

        // ------------------------------------------------------------------
        // Build dev_agent_cfg: DEVICE/SERIAL_IF HS agent.
        //
        // Cross-reference pattern from SVT b2b_phy example:
        //   dev_agent_cfg.remote_host_cfg    = dummy_host_cfg.local_host_cfg
        //   dev_agent_cfg.remote_device_cfg_size = 0
        //   dummy_host_cfg.remote_device_cfg = dev_agent_cfg.local_device_cfg
        // ------------------------------------------------------------------
        dev_agent_cfg = new("dev_agent_cfg");
        dev_agent_cfg.component_type          = svt_usb_types::DEVICE;
        dev_agent_cfg.top_layer               = svt_usb_agent_configuration::PROTOCOL;

        // DEVICE on USB_20_SERIAL_IF -- connects to DUT HOST via nvs_usb_phy.
        dev_agent_cfg.usb_20_signal_interface = svt_usb_configuration::USB_20_SERIAL_IF;
        dev_agent_cfg.usb_ss_signal_interface = svt_usb_configuration::NO_SS_IF;
        dev_agent_cfg.usb_capability          = svt_usb_configuration::USB_20_ONLY;
        dev_agent_cfg.capability              = svt_usb_configuration::PLAIN;
        dev_agent_cfg.speed                   = svt_usb_types::HS;

        dev_agent_cfg.local_host_cfg = null;

        // Cross-references (SVT b2b_phy pattern).
        dev_agent_cfg.remote_host_cfg        = dummy_host_cfg.local_host_cfg;
        dev_agent_cfg.remote_device_cfg_size = 0;

        // Auto-attach at 10 us (before DUT sets PP+PR).
        dev_agent_cfg.poweron_auto_attach_delay = 10_000_000.0; // 10 us in ps

        // One device configuration entry.
        dev_agent_cfg.local_device_cfg_size = 1;
        dev_agent_cfg.local_device_cfg[0]   = new();

        // Device address 1 (matches ISO PTD DW1 DevAddr field).
        dev_agent_cfg.local_device_cfg[0].device_address               = 7'd1;
        dev_agent_cfg.local_device_cfg[0].connected_hub_device_address = 7'd0;

        // HS capable. high_speed_capable=1 keeps the VIP in PERIPHERAL_HI_SPEED
        // after BUS_RESET exit (same issue as bulk OUT test).
        dev_agent_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::HS;
        dev_agent_cfg.local_device_cfg[0].functionality_support = svt_usb_types::HS;
        dev_agent_cfg.local_device_cfg[0].high_speed_capable    = 1'b1;

        // EP0 CONTROL + EP1 ISO OUT + EP2 ISO IN.
        dev_agent_cfg.local_device_cfg[0].num_endpoints = 3;

        // 60 ms timeout: covers enum (~4 ms) + 2x ISO OUT + 2x ISO IN (~4 more frames).
        dev_agent_cfg.local_device_cfg[0].device_timeout = 60_000_000_000.0; // 60 ms in ps

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

        // EP1: ISOCHRONOUS OUT, HS 1024-byte (DUT HOST sends, VIP DEVICE receives).
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1]                 = new();
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::OUT;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::ISOCHRONOUS;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].max_burst_size  = 0;
        // HS isochronous max packet size = 1024 bytes (USB 2.0 spec table 5-4).
        // SVT VIP does not define a SVT_USB_HS_ISO_MAX_PACKET_SIZE macro.
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = 1024;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[1].speed = svt_usb_types::HS;

        // EP2: ISOCHRONOUS IN, HS 1024-byte (DUT HOST requests, VIP DEVICE sends data).
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2]                 = new();
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2].ep_number       = 2;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2].direction       = svt_usb_types::IN;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2].ep_type         = svt_usb_types::ISOCHRONOUS;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2].interval        = 1;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2].max_burst_size  = 0;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2].max_packet_size = 1024;
        dev_agent_cfg.local_device_cfg[0].endpoint_cfg[2].speed           = svt_usb_types::HS;

        // Complete dummy_host_cfg cross-references.
        dummy_host_cfg.remote_device_cfg_size = dev_agent_cfg.local_device_cfg_size;
        dummy_host_cfg.remote_device_cfg      = dev_agent_cfg.local_device_cfg;
        dummy_host_cfg.remote_host_cfg        = dev_agent_cfg.local_host_cfg; // null

        // Apply VIP scaledown timer preset, then override critical timers.
        void'(dev_agent_cfg.set_timer_values(
            svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));

        // tsigatt: debounce after J-state / D+ pull-up detected.
        dev_agent_cfg.tsigatt = 100_000_000.0;   // 100 us in ps

        // tdrst: time DEVICE waits after detecting SE0 before firing chirp-K.
        dev_agent_cfg.tdrst = 50_000_000.0;      // 50 us in ps

        // twtrev: allow ample time for DUT to issue first HS SOF after ISO_EN.
        // ISO PTD fires on first SOF after ISO_EN -- timing is similar to bulk.
        dev_agent_cfg.twtrev = 10_000_000_000.0; // 10 ms in ps

        // tddis: must exceed HS SOF period + ISO frame window.
        dev_agent_cfg.tddis = 5_000_000_000.0;   // 5 ms in ps

        // tinactivity: prevent SUSPENDED before DUT sends ISO tokens (~4+ ms).
        dev_agent_cfg.tinactivity = 10_000_000_000.0; // 10 ms in ps

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
            "dev_agent_cfg (DEVICE/SERIAL_IF/HS): addr=1, EP1=ISO OUT 1024B, tdrst=50us, attach=10us",
            UVM_LOW)
        `uvm_info("build_phase", "Exiting...", UVM_LOW)
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
            "======= VIP device agent configuration dump (ISO OUT test) =======",
            UVM_LOW)

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
            dcfg.poweron_auto_attach_delay,
            dcfg.poweron_auto_attach_delay/1.0e6), UVM_LOW)

        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_prot_tracing            = %0b", dcfg.enable_prot_tracing), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_link_tracing            = %0b", dcfg.enable_link_tracing), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_phys_tracing            = %0b", dcfg.enable_phys_tracing), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_phys_reporting          = %0b", dcfg.enable_phys_reporting), UVM_LOW)
        `uvm_info("VIP_CFG_DUMP", $sformatf(
            "  enable_runtime_trace_recording = %0b",
            dcfg.enable_runtime_trace_recording), UVM_LOW)

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
                "  local_device_cfg[%0d].device_address         = %0d",
                i, devcfg.device_address), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].connected_bus_speed    = %s",
                i, devcfg.connected_bus_speed.name()), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].functionality_support  = %s",
                i, devcfg.functionality_support.name()), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].high_speed_capable     = %0b",
                i, devcfg.high_speed_capable), UVM_LOW)
            `uvm_info("VIP_CFG_DUMP", $sformatf(
                "  local_device_cfg[%0d].num_endpoints          = %0d",
                i, devcfg.num_endpoints), UVM_LOW)
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

        `uvm_info("VIP_CFG_DUMP",
            "======= end VIP device agent configuration dump =======", UVM_LOW)
    endfunction

    // -------------------------------------------------------------------------
    // run_phase: start the ISO OUT device sequence explicitly.
    // -------------------------------------------------------------------------
    virtual task run_phase(uvm_phase phase);
        caliptra_ss_usb_hs_host_iso_out_sequence seq;

        phase.raise_objection(this, "USB HS host ISO OUT sequence running");

        `uvm_info("run_phase",
            "Starting caliptra_ss_usb_hs_host_iso_out_sequence on host_agent.virt_sequencer",
            UVM_LOW)

        seq = caliptra_ss_usb_hs_host_iso_out_sequence::type_id::create("seq");
        seq.start(env.host_agent.virt_sequencer);

        `uvm_info("run_phase",
            "caliptra_ss_usb_hs_host_iso_out_sequence completed.", UVM_LOW)

        phase.drop_objection(this, "USB HS host ISO OUT sequence done");
    endtask

endclass

`endif // CALIPTRA_SS_USB_HS_HOST_ISO_OUT_TEST_SV
