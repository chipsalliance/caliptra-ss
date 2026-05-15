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

`ifndef CALIPTRA_SS_USB_SHARED_CFG_SV
`define CALIPTRA_SS_USB_SHARED_CFG_SV

`ifndef CALIPTRA_SS_USB_CFG_TIMEOUT
`define CALIPTRA_SS_USB_CFG_TIMEOUT 10ms
`endif

// =============================================================================
// USB shared configuration for Caliptra Subsystem testbench.
//
// The UVM environment builds one host_agent. host_cfg configures the local host
// stack. dev_cfg is not used to create a second agent; it is the template that
// env clones into remote_cfg, which represents the device PHY connected to the
// DUT through one svt_usb_if UTMI+ interface.
//
// Two configuration objects are built and linked, mirroring usb_shared_cfg.sv
// in the VIP example:
//   - host_cfg : component_type=HOST,   usb_20_signal_interface=USB_20_TLM
//   - dev_cfg  : component_type=DEVICE, usb_20_signal_interface=UTMI_IF
// The env clones dev_cfg and overrides component_subtype=PHY to produce
// remote_cfg, which it pushes to host_agent's "remote_cfg" config_db slot.
// =============================================================================
class caliptra_ss_usb_shared_cfg extends uvm_object;

    real timeout = `CALIPTRA_SS_USB_CFG_TIMEOUT;

    localparam real USB_TIMER_10US_PS  = 10000000.0;
    localparam real USB_TIMER_20US_PS  = 20000000.0;
    localparam real USB_TIMER_50US_PS  = 50000000.0;
    localparam real USB_TIMER_100US_PS = 100000000.0;
    localparam real USB_TIMER_150US_PS = 150000000.0;
    localparam real USB_TIMER_300US_PS = 300000000.0;

    // host_cfg drives host_agent; dev_cfg is cloned into host_agent.remote_cfg.
    svt_usb_agent_configuration host_cfg;
    svt_usb_agent_configuration dev_cfg;

    // Number of endpoints to configure on the device (DUT)
    int num_endpoints = 2;

    `uvm_object_utils_begin(caliptra_ss_usb_shared_cfg)
        `uvm_field_object(host_cfg, UVM_ALL_ON|UVM_DEEP)
        `uvm_field_object(dev_cfg,  UVM_ALL_ON|UVM_DEEP)
        `uvm_field_real  (timeout,  UVM_ALL_ON)
        `uvm_field_int   (num_endpoints, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "caliptra_ss_usb_shared_cfg");
        super.new(name);

        host_cfg = new();
        dev_cfg  = new();

        host_cfg.component_type            = svt_usb_types::HOST;
        dev_cfg.component_type             = svt_usb_types::DEVICE;

        // Run the full VIP stack so link services can perform attach/reset and
        // the protocol sequencer can issue enumeration transfers.
        host_cfg.top_layer                                = svt_usb_agent_configuration::PROTOCOL;
        dev_cfg.top_layer                                 = svt_usb_agent_configuration::PROTOCOL;

        host_cfg.local_host_cfg            = new();
        // Enable HS chirp negotiation by the host VIP. Per VIP doc
        // (svt_usb_host_configuration::high_speed_capable), default is 0
        // which forces the post-reset bus speed to FS or LS even if the
        // peripheral is HS-capable. Set to 1 so the host attempts HS.
        host_cfg.local_host_cfg.high_speed_capable = 1'b1;
        host_cfg.local_device_cfg_size     = 0;

        dev_cfg.local_device_cfg_size      = 1;
        dev_cfg.local_device_cfg[0]        = new();
        dev_cfg.local_host_cfg             = null;

        // Link host_cfg's remote device view to the device template used for
        // remote_cfg.
        host_cfg.remote_device_cfg_size = dev_cfg.local_device_cfg_size;
        host_cfg.remote_device_cfg      = dev_cfg.local_device_cfg;
        host_cfg.remote_host_cfg        = dev_cfg.local_host_cfg;

        dev_cfg.remote_host_cfg         = host_cfg.local_host_cfg;
        dev_cfg.remote_device_cfg_size  = host_cfg.local_device_cfg_size;

    endfunction

    // -------------------------------------------------------------------------
    // USB 2.0 HS setup for one host_agent plus remote_cfg device PHY.
    // -------------------------------------------------------------------------
    function void setup_usb_20_utmi_host_defaults();
        // -------------------- host_cfg (HOST, USB_20_TLM) --------------------
        host_cfg.capability                = svt_usb_configuration::PLAIN;
        host_cfg.speed                     = svt_usb_types::HS;
        host_cfg.usb_20_signal_interface   = svt_usb_configuration::USB_20_TLM;
        host_cfg.usb_ss_signal_interface   = svt_usb_configuration::NO_SS_IF;
        host_cfg.usb_capability            = svt_usb_configuration::USB_20_ONLY;
        host_cfg.utmi_data_width           = 8;
        host_cfg.poweron_auto_attach_delay = USB_TIMER_20US_PS;

        // -------------------- dev_cfg (DEVICE, UTMI_IF) ----------------------
        dev_cfg.capability                 = svt_usb_configuration::PLAIN;
        dev_cfg.speed                      = svt_usb_types::HS;
        dev_cfg.usb_20_signal_interface    = svt_usb_configuration::UTMI_IF;
        dev_cfg.usb_ss_signal_interface    = svt_usb_configuration::NO_SS_IF;
        dev_cfg.usb_capability             = svt_usb_configuration::USB_20_ONLY;
        dev_cfg.utmi_data_width            = 8;
        // Auto-attach at 100 us, after DUT firmware has initialized the
        // controller and enabled the full-speed pull-up.
        dev_cfg.poweron_auto_attach_delay  = USB_TIMER_20US_PS;

        // local_device_cfg[0]: HS-capable device attaching initially as FS
        // (USB 2.0 sec 7.1.7.1) then upgrading to HS via chirp K-J-K-J.
        dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::HS;
        dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::HS;
//        dev_cfg.local_device_cfg[0].high_speed_capable    = 1'b1;
        dev_cfg.local_device_cfg[0].device_address        = 0;
        dev_cfg.local_device_cfg[0].connected_hub_device_address = 0;
        dev_cfg.local_device_cfg[0].num_endpoints         = num_endpoints;
        // Increase device_timeout to allow MCU firmware time to process
        // SETUP packets and prime endpoint buffers. Default scaledown
        // value is too aggressive for firmware-driven responses.
        dev_cfg.local_device_cfg[0].device_timeout        = 50us;

        for (int ep = 0; ep < num_endpoints; ep++) begin
            dev_cfg.local_device_cfg[0].endpoint_cfg[ep] = new();
        end
        // EP0: CONTROL
        if (num_endpoints >= 1) begin
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].ep_number       = 0;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].direction       = svt_usb_types::IN;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].ep_type         = svt_usb_types::CONTROL;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].interval        = 1;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_burst_size  = 0;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_HS_CONTROL_MAX_PACKET_SIZE;
            dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::HS;
        end
        // EP1: BULK IN
        if (num_endpoints >= 2) begin
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_number       = 1;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::IN;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].ep_type         = svt_usb_types::BULK;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].interval        = 1;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_HS_BULK_MAX_PACKET_SIZE;
            dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::HS;
        end

        // -------------------- Scaled-down timers -----------------------------
        void'(host_cfg.set_timer_values(svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));
        void'(dev_cfg.set_timer_values (svt_usb_configuration::USB_VIP_SCALEDOWN_TIMER_VALUES));

        // -------------------- Link-up timer overrides ------------------------
        // tsigatt: signal attach debounce. Auto-attach fires at 20 us so the
        // PHY is connected before the DUT asserts FS pull-up at ~37 us. The
        // 100 us tsigatt adds debounce after the host sees D+ high.
        host_cfg.tsigatt = USB_TIMER_100US_PS;
        dev_cfg.tsigatt  = USB_TIMER_100US_PS;

        // tdrst: host SE0 reset duration. 150 us is the only value proven
        // to trigger the VIP HOST_CHIRP code path (chirp_k_detection via
        // UTMI TLM). The DUT chirp timers (T_CHIRP_DELAY=10 us, T_TUCH=30 us)
        // are scaled to fit the full handshake within this window:
        //   10 us pre-chirp + 30 us chirp K + ~24 us K-J = ~64 us.
        host_cfg.tdrst   = USB_TIMER_150US_PS;
        dev_cfg.tdrst    = USB_TIMER_150US_PS;
        host_cfg.twtdch  = USB_TIMER_10US_PS;
        dev_cfg.twtdch   = USB_TIMER_10US_PS;
        host_cfg.twths   = USB_TIMER_10US_PS;
        dev_cfg.twths    = USB_TIMER_10US_PS;

        // tinactivity: bus-idle duration before the VIP enters SUSPENDED.
        // The scaledown default is ~6 us which is shorter than the scaled
        // SOF interval, causing premature suspend between SOF frames.
        // 300 us gives ample room for SOF keep-alive packets.
        host_cfg.tinactivity = USB_TIMER_300US_PS;
        dev_cfg.tinactivity  = USB_TIMER_300US_PS;

        // Protocol- and link-layer trace logging to dedicated log files.
        // enable_prot_tracing: writes svt_usb_transfer objects per transaction.
        // enable_link_tracing: writes svt_usb_packet objects per packet.
        // enable_runtime_trace_recording: enables monitor-side runtime capture.
        // Applied to both host_cfg and dev_cfg so both the host agent stack
        // and the remote_cfg PHY model produce trace output.
        // enable_phys_tracing explicitly set to 0 to suppress physical-layer
        // trace files even if +svt_debug_opts enables them by default.
        host_cfg.enable_prot_tracing            = 1;
        host_cfg.enable_link_tracing            = 1;
        host_cfg.enable_phys_tracing            = 1;
        host_cfg.enable_phys_reporting          = 1;
        host_cfg.enable_runtime_trace_recording = 1;
        dev_cfg.enable_prot_tracing             = 1;
        dev_cfg.enable_link_tracing             = 1;
        dev_cfg.enable_phys_tracing             = 1;
        dev_cfg.enable_phys_reporting           = 1;
        dev_cfg.enable_runtime_trace_recording  = 1;
    endfunction

    /**
     * Checks to see that the data field values are valid, mainly making sure the
     * host and device interface specifications are consistent. 
     */
    virtual function bit is_valid(bit silent = 1, int kind = -1);
        begin
            is_valid = 1;
      
            if (!host_cfg.is_valid()) begin
                if (!silent) begin
                    `uvm_info("is_valid", $sformatf("Invalid Host configuration. Contents:\n%s", host_cfg.sprint()), UVM_HIGH)
                end
                is_valid = 0;   
            end else if (!dev_cfg.is_valid()) begin
                if (!silent) begin
                    `uvm_info("is_valid", $sformatf("Invalid Device configuration. Contents:\n%s", dev_cfg.sprint()), UVM_HIGH);
                end
                is_valid = 0;   
            end
        end
    endfunction

endclass

`endif // CALIPTRA_SS_USB_SHARED_CFG_SV
