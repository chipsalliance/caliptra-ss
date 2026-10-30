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

    // Per-transaction device response timeout applied to every USB 2.0
    // speed/transfer-type combination. This bounds how long the host waits
    // for *a* response (any handshake) to a single transaction; it does NOT
    // bound how many times a NAKed transaction is re-tried. The retry count
    // is a separate, count-based budget - see
    // USB_EP_MAX_RETRY_DUE_TO_NAK below.
    localparam real USB_20_DEVICE_RESPONSE_TIMEOUT = 200us;

    // Number of times the host VIP re-tries a transaction that the device
    // answers with NAK before it gives up and marks the whole transfer
    // ABORTED. This is the budget that actually governs NAK retry.
    //
    // svt_usb_endpoint_configuration::max_retry_due_to_nak defaults to 10,
    // which is 1 initial attempt + 10 retries = 11 NAKs. That is exactly
    // what the VIP trace shows before it aborts:
    //
    //   <Dev:2 EP:0 CONTROL HS> [check_20_xact_complete] [Xact:1] - Transaction ENDED ...
    //   <Dev:2 EP:0 CONTROL HS> [check_20_xfer_complete] - Transfer ABORTED ...
    //   [transfer_ended] This transfer completed with results_status[127:0] = 128'b0
    //
    // The abort is a budget exhaustion, not a protocol error, which is why
    // results_status is all-zero and why no timeout knob can prevent it:
    // every one of the 11 transactions got a prompt, legal NAK well inside
    // the device timeout ([device_timeout_check] passes each time, and
    // [complete_device_response] reports "no observed or injected errors").
    //
    // The DUT is software-polled MCU firmware. A control request can easily
    // need more than 11 polling intervals before the firmware has primed the
    // EP0 buffer, so 10 retries is too small a budget here and produces a
    // false failure on a device that does eventually answer correctly.
    //
    // 500 is chosen to sit well above the deepest NAK burst actually observed
    // while still letting a genuinely dead endpoint fail in bounded time. The
    // measured bursts on the hotplug test (dev0 enumeration + 3 reconnect
    // cycles, software-polled firmware) peaked at 11 NAKs over ~4.9 us, i.e.
    // roughly 450 ns per NAK, so 500 retries is a ~45x margin on the real
    // worst case and costs at most ~225 us per genuinely wedged transfer.
    localparam int USB_EP_MAX_RETRY_DUE_TO_NAK = 500;

    // host_cfg drives host_agent; dev_cfg is cloned into host_agent.remote_cfg.
    svt_usb_agent_configuration host_cfg;
    svt_usb_agent_configuration dev_cfg;

    // Number of endpoints to configure on the device (DUT)
    int num_endpoints = 2;

    // -------------------------------------------------------------------------
    // OCP Recovery interface number (bInterfaceNumber) used by the host when
    // issuing class-specific requests per OCP Recovery v1.1 sec 8.5.2.
    // Row 2 ("wIndex") of Table "Setup Packet" RECOMMENDS 00h for the
    // recovery interface number; any 8-bit value is legal so no validation
    // is required in is_valid(). Override via test if the firmware-built
    // configuration descriptor places the recovery interface elsewhere.
    //
    // EP0-only architecture: all OCP class transfers ride on the default
    // control pipe (EP0). Per OCP v1.1 sec 8.5 there are no bulk endpoints
    // associated with recovery.
    // -------------------------------------------------------------------------
    int unsigned ocp_recovery_iface_num = 0;

    `uvm_object_utils_begin(caliptra_ss_usb_shared_cfg)
        `uvm_field_object(host_cfg, UVM_ALL_ON|UVM_DEEP)
        `uvm_field_object(dev_cfg,  UVM_ALL_ON|UVM_DEEP)
        `uvm_field_real  (timeout,  UVM_ALL_ON)
        `uvm_field_int   (num_endpoints, UVM_ALL_ON)
        `uvm_field_int   (ocp_recovery_iface_num, UVM_ALL_ON)
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
        // Auto-attach at 20 us. Note this is BEFORE the DUT firmware has
        // initialized the controller: firmware only reaches
        // usb_hub_connect() (HUB_EN|HUB_CONNECT) at 55-70 us, so VBus is
        // already present for the whole of USB bring-up in every test that
        // takes this default. caliptra_ss_usb_hs_dev_vbus_absent_boot_test
        // overrides this to 150 us to get the opposite ordering.
        dev_cfg.poweron_auto_attach_delay  = USB_TIMER_20US_PS;

        // local_device_cfg[0]: HS-capable device attaching initially as FS
        // (USB 2.0 sec 7.1.7.1) then upgrading to HS via chirp K-J-K-J.
        dev_cfg.local_device_cfg[0].connected_bus_speed   = svt_usb_types::HS;
        dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::HS;
//        dev_cfg.local_device_cfg[0].high_speed_capable    = 1'b1;
        dev_cfg.local_device_cfg[0].device_address        = 0;
        // This device model (Dev1 in the caliptra-ss topology) is attached
        // behind the embedded ip_xxx_3511_hs_mem_compound hub's downstream
        // port 1. connected_hub_device_address=0 tells the VIP the parent hub
        // is addressed at device address 0 (the hub's own control endpoint,
        // matching the addressing convention used before SET_ADDRESS(1) is
        // issued). hub_port_number=1 associates this device with hub
        // downstream port 1, consistent with the SetPortFeature/
        // ClearPortFeature(port=1) Hub Class bring-up sequence issued from
        // caliptra_ss_usb_hs_dev_bulk_out_sequence.svh (hub_port_bringup()).
        dev_cfg.local_device_cfg[0].connected_hub_device_address = 0;
        dev_cfg.local_device_cfg[0].hub_port_number        = 1;
        dev_cfg.local_device_cfg[0].num_endpoints         = num_endpoints;

        // Increase device_timeout to allow MCU firmware time to process
        // SETUP packets and prime endpoint buffers. Default scaledown
        // value is too aggressive for firmware-driven responses.
        dev_cfg.local_device_cfg[0].device_timeout        = 50us;

        for (int ep = 0; ep < num_endpoints; ep++) begin
            dev_cfg.local_device_cfg[0].endpoint_cfg[ep] = new();

            // Raise the NAK retry budget on every endpoint. The VIP default
            // of 10 aborts the transfer after 11 NAKs, which a software
            // polled device routinely exceeds while its firmware is still
            // getting round to the request. See USB_EP_MAX_RETRY_DUE_TO_NAK.
            //
            // max_retry_due_to_nak is declared rand and the VIP carries a
            // reasonable_max_retry constraint pinning it to 10, but these
            // endpoint configurations are populated by direct assignment and
            // randomize() is never called on them, so the assignment stands.
            dev_cfg.local_device_cfg[0].endpoint_cfg[ep].max_retry_due_to_nak =
                USB_EP_MAX_RETRY_DUE_TO_NAK;

            // Keep the "move to the next endpoint" threshold below the abort
            // budget. The VIP documents that if this is not strictly less
            // than max_retry_due_to_nak the transfer is aborted before the
            // bus access algorithm ever gets a chance to run.
            dev_cfg.local_device_cfg[0].endpoint_cfg[ep].max_retry_due_to_nak_before_moving_to_next_ep =
                USB_EP_MAX_RETRY_DUE_TO_NAK / 2;
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

        // ---------------- USB 2.0 per-transaction device timeouts -----------
        // Applied after set_timer_values() so the scaledown pass cannot put
        // the spec-derived defaults back.
        //
        // These are the knobs that actually bound how long the host VIP keeps
        // re-trying a transaction the device is answering with NAK. They are
        // selected by speed AND transfer type, and are entirely separate from
        // svt_usb_device_configuration::device_timeout, which is a whole
        // transfer abort deadline whose documented fallback is the SuperSpeed
        // constant SVT_USB_SS_T_HOST_TRANSACTION_TIMEOUT. This testbench runs
        // USB 2.0 HS/FS only, so device_timeout is not the control that
        // governs NAK retry here.
        //
        // The VIP defaults (svt_usb_timing_defines.svi) are spec-derived and
        // far too tight for a software-polled MCU device, which only services
        // a SETUP or primes an endpoint buffer when its polling loop next
        // runs:
        //
        //   usb_20_device_timeout_control_hs         1.8  us
        //   usb_20_device_timeout_bulk_hs           10.5  us
        //   usb_20_device_timeout_interrupt_hs      20.5  us
        //   usb_20_device_timeout_isoc_hs           20.5  us
        //   usb_20_device_timeout_non_isoc_fs       54    us
        //   usb_20_device_timeout_non_isoc_ls       79    us
        //   usb_20_utmi_device_timeout_control_hs    1.95 us
        //   usb_20_utmi_device_timeout_bulk_hs      10.65 us
        //   usb_20_utmi_device_timeout_non_isoc_fs  54.5  us
        //   usb_20_utmi_device_timeout_non_isoc_ls  82    us
        //
        // Raising these was originally expected to also fix the "11 NAKs then
        // abort" failure. It did not: with every value at 200 us the abort
        // still happened, deterministically, within 17 ns of where it
        // happened before. The VIP trace shows why - each NAK arrives
        // promptly and legally, [device_timeout_check] passes every time, and
        // the abort comes from the count-based retry budget instead. That is
        // handled by USB_EP_MAX_RETRY_DUE_TO_NAK. These timeouts are still
        // raised because a software-polled device can legitimately be slow to
        // answer at all, which is exactly what they bound.
        //
        // usb_20_device_timeout_isoc_fs is deliberately left at its 800 us
        // default, which is already larger than the budget and must not be
        // reduced.
        host_cfg.usb_20_device_timeout_control_hs       = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_device_timeout_bulk_hs          = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_device_timeout_interrupt_hs     = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_device_timeout_isoc_hs          = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_device_timeout_non_isoc_fs      = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_device_timeout_non_isoc_ls      = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_utmi_device_timeout_control_hs  = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_utmi_device_timeout_bulk_hs     = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_utmi_device_timeout_non_isoc_fs = USB_20_DEVICE_RESPONSE_TIMEOUT;
        host_cfg.usb_20_utmi_device_timeout_non_isoc_ls = USB_20_DEVICE_RESPONSE_TIMEOUT;

        // The device agent models the peripheral side of the same bus; keep
        // its view of these timeouts consistent with the host's.
        dev_cfg.usb_20_device_timeout_control_hs        = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_device_timeout_bulk_hs           = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_device_timeout_interrupt_hs      = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_device_timeout_isoc_hs           = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_device_timeout_non_isoc_fs       = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_device_timeout_non_isoc_ls       = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_utmi_device_timeout_control_hs   = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_utmi_device_timeout_bulk_hs      = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_utmi_device_timeout_non_isoc_fs  = USB_20_DEVICE_RESPONSE_TIMEOUT;
        dev_cfg.usb_20_utmi_device_timeout_non_isoc_ls  = USB_20_DEVICE_RESPONSE_TIMEOUT;

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

        // VIP tracing and debug reporting are disabled by default. Enable them
        // for a specific run with +svt_debug_opts.
        //host_cfg.enable_prot_tracing            = 1;
        //host_cfg.enable_link_tracing            = 1;
        //host_cfg.enable_phys_tracing            = 1;
        //host_cfg.enable_phys_reporting          = 1;
        //host_cfg.enable_runtime_trace_recording = 1;
        //dev_cfg.enable_prot_tracing             = 1;
        //dev_cfg.enable_link_tracing             = 1;
        //dev_cfg.enable_phys_tracing             = 1;
        //dev_cfg.enable_phys_reporting           = 1;
        //dev_cfg.enable_runtime_trace_recording  = 1;

        // Built-in VIP protocol and link layer functional coverage.
        host_cfg.enable_prot_cov                = 1;
        host_cfg.enable_link_cov                = 1;
        dev_cfg.enable_prot_cov                 = 1;
        dev_cfg.enable_link_cov                 = 1;
    endfunction

    // -------------------------------------------------------------------------
    // add_remote_device_slot
    //
    // Append ONE additional, PERSISTENT remote-device configuration slot to
    // host_cfg.remote_device_cfg[$] at the given bus address, cloning the
    // endpoint layout of slot 0. Returns the new slot's index, which callers
    // pass to do_data_xfer() as dev_anchor_idx.
    //
    // WHY THIS EXISTS - THE DATA TOGGLE.
    //
    // remote_device_cfg[$] is a queue and the VIP fully supports several
    // remote devices at once: svt_usb_configuration constrains each populated
    // entry to a DISTINCT device_address, and the VIP's own example sequences
    // address them with fix_anchors(1,0,0) / fix_anchors(tier,0,0).
    //
    // With only ONE slot available a multi-device test has to retarget that
    // slot between transfers:
    //
    //     remote_device_cfg[0].device_address = addr;
    //     host_agent_h.reconfigure(usb_cfg);
    //
    // That retarget is DESTRUCTIVE. reconfigure() tears down and rebuilds the
    // endpoint protocol processors, and a freshly built BULK endpoint starts
    // its DATA TOGGLE AT DATA0. USB 2.0 section 8.6 makes that fatal but
    // SILENT: a conformant device advances its own toggle after each accepted
    // OUT, so once the device expects DATA1 and the host restarts at DATA0 the
    // device treats the packet as a presumed retransmission and DISCARDS it -
    // no buffer write, no descriptor retire, no completion interrupt. The host
    // then NAKs on the paired IN until its retry budget is exhausted and the
    // transfer is reported ABORTED with results_status == 0.
    //
    // MEASURED EVIDENCE (dev0 hotplug test, USBDC1 EP1 BULK OUT; taken from
    // the "ep_type=BULK ... pid_transmitted=" records in svt_debug.transcript):
    //
    //   OUT  time (ns)   PID sent   device expected   endpoint xactor
    //    1     742336      DATA0         DATA0        created 688405
    //    2     785935      DATA1         DATA1        SAME instance, reused
    //    3    1270982      DATA0         DATA0        fresh @1269418
    //    4    1751246      DATA0        *DATA1*       fresh @1749682  <- FAIL
    //
    // Every fresh xactor restarts at DATA0. OUT 2 happened to reuse a
    // surviving instance and so advanced correctly; OUT 1 and OUT 3 were
    // COINCIDENTALLY correct because DATA0 was what the device wanted anyway.
    // OUT 4 is the first transfer where DATA1 was expected, and therefore the
    // first one where the toggle reset is observable at all - which is exactly
    // why three bulk loopbacks passed and only the fourth died. The failure is
    // a testbench artefact; RTL and firmware both behaved correctly.
    //
    // Giving every device on the bus its own persistent slot removes the need
    // to retarget, so the endpoint xactors live for the whole run and their
    // toggles advance continuously.
    //
    // SCOPE - READ BEFORE ADDING A reconfigure(). This does NOT make
    // reconfigure() safe to call again. Any reconfigure() still rebuilds EVERY
    // endpoint xactor and so resets EVERY toggle, including those of devices
    // the caller was not touching. Enumeration still legitimately retargets
    // and reconfigures slot 0 because SET_ADDRESS genuinely changes an
    // address, so it must run BEFORE any bulk stream that must not be
    // disturbed.
    // -------------------------------------------------------------------------
    function int add_remote_device_slot(bit [6:0] device_address);
        svt_usb_device_configuration src;
        svt_usb_device_configuration slot;
        int                          idx;

        if (host_cfg == null || host_cfg.remote_device_cfg.size() < 1) begin
            `uvm_error("add_remote_device_slot",
                "host_cfg.remote_device_cfg[0] must exist before cloning it.")
            return 0;
        end

        src  = host_cfg.remote_device_cfg[0];
        slot = new();

        // Mirror the attributes describing how the device sits on the bus.
        // device_address MUST be distinct from every other populated slot:
        // svt_usb_configuration constrains i != j -> addr[i] != addr[j], so a
        // duplicate makes the configuration unsatisfiable.
        slot.device_address               = device_address;
        slot.connected_bus_speed          = src.connected_bus_speed;
        slot.functionality_support        = src.functionality_support;
        slot.connected_hub_device_address = src.connected_hub_device_address;
        slot.hub_port_number              = src.hub_port_number;
        slot.device_timeout               = src.device_timeout;
        slot.num_endpoints                = src.num_endpoints;

        // Clone the endpoint layout, including the NAK retry budget. These are
        // FRESH objects, not shared handles - two slots sharing one endpoint
        // configuration would defeat the entire purpose of separate slots.
        for (int ep = 0; ep < src.num_endpoints; ep++) begin
            if (src.endpoint_cfg[ep] == null) continue;
            slot.endpoint_cfg[ep] = new();
            slot.endpoint_cfg[ep].ep_number       = src.endpoint_cfg[ep].ep_number;
            slot.endpoint_cfg[ep].direction       = src.endpoint_cfg[ep].direction;
            slot.endpoint_cfg[ep].ep_type         = src.endpoint_cfg[ep].ep_type;
            slot.endpoint_cfg[ep].speed           = src.endpoint_cfg[ep].speed;
            slot.endpoint_cfg[ep].interval        = src.endpoint_cfg[ep].interval;
            slot.endpoint_cfg[ep].max_packet_size = src.endpoint_cfg[ep].max_packet_size;
            slot.endpoint_cfg[ep].max_burst_size  = src.endpoint_cfg[ep].max_burst_size;
            slot.endpoint_cfg[ep].allow_aligned_transfer_without_zero_length =
                src.endpoint_cfg[ep].allow_aligned_transfer_without_zero_length;
            slot.endpoint_cfg[ep].max_retry_due_to_nak =
                USB_EP_MAX_RETRY_DUE_TO_NAK;
            slot.endpoint_cfg[ep].max_retry_due_to_nak_before_moving_to_next_ep =
                USB_EP_MAX_RETRY_DUE_TO_NAK / 2;
        end

        host_cfg.remote_device_cfg.push_back(slot);
        host_cfg.remote_device_cfg_size = host_cfg.remote_device_cfg.size();
        idx = host_cfg.remote_device_cfg_size - 1;

        `uvm_info("add_remote_device_slot",
            $sformatf({"Added persistent remote_device_cfg[%0d] at device ",
                       "address %0d (%0d endpoints cloned from slot 0)."},
                      idx, device_address, src.num_endpoints), UVM_LOW)
        return idx;
    endfunction

    // -------------------------------------------------------------------------
    // apply_nak_retry_budget
    //
    // Re-applies USB_EP_MAX_RETRY_DUE_TO_NAK to every currently allocated
    // endpoint configuration.
    //
    // setup_usb_20_utmi_host_defaults() already does this for the endpoints it
    // allocates itself, but several tests add further endpoints (typically
    // endpoint_cfg[2], a BULK OUT) in their own build_phase, which runs after
    // the shared setup. Those endpoint objects do not exist yet at that point,
    // so they would otherwise keep the VIP default of 10 and remain exposed to
    // the spurious "11 NAKs then ABORTED" failure.
    //
    // A test that allocates extra endpoints should call this at the end of its
    // build_phase. It is idempotent and safe to call more than once.
    //
    // agent_cfg defaults to this object's own dev_cfg, which is what the
    // cfg.dev_cfg-based tests want. The hs_host_* tests instead build their
    // own local svt_usb_agent_configuration (dev_agent_cfg) that is not
    // reachable from here, so they pass that handle in explicitly.
    // -------------------------------------------------------------------------
    function void apply_nak_retry_budget(
        svt_usb_agent_configuration agent_cfg = null);

        svt_usb_device_configuration dev_view;

        if (agent_cfg == null) agent_cfg = dev_cfg;

        if (agent_cfg == null)                   return;
        if (agent_cfg.local_device_cfg_size < 1) return;

        dev_view = agent_cfg.local_device_cfg[0];
        if (dev_view == null) return;

        for (int ep = 0; ep < dev_view.num_endpoints; ep++) begin
            if (dev_view.endpoint_cfg[ep] == null) continue;

            dev_view.endpoint_cfg[ep].max_retry_due_to_nak =
                USB_EP_MAX_RETRY_DUE_TO_NAK;
            dev_view.endpoint_cfg[ep].max_retry_due_to_nak_before_moving_to_next_ep =
                USB_EP_MAX_RETRY_DUE_TO_NAK / 2;
        end
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
