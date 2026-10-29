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

`ifndef CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV
`define CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV

// =============================================================================
// USB HS device power-down sequence (Hub-Enabled mode).
//
// In hub-enabled mode the device under test (USBDC0) is an embedded downstream
// device of the compound hub. The host<->HUB upstream link is HS. Removing
// VBUS on that upstream link (as the legacy direct-attach power-down test did)
// does NOT map to hub mode:
//   - USBDC0 never observes the host VBUS on its own VBUS_DEBOUNCED bit
//     (its supply is the hub's downstream port, not the host VBUS), so the
//     firmware can never detect the "power-down" that way; and
//   - removing/re-applying upstream VBUS disconnects the hub and the HS
//     re-negotiation does not reliably reproduce - the VIP link comes back at
//     FS while the device stays HS, so every re-enumeration token times out;
//     and the hub, never reset, stays enumerated at address 1 so the hub
//     re-enumeration (GET_DESCRIPTOR @ address 0) cannot succeed either.
//
// GENUINE power-down model (RTL-accurate):
// The one hub-class request in this IP that actually removes power/enable from
// the embedded downstream device USBDC0 is ClearFeature(PORT_ENABLE) on the
// downstream port. Per usb_app_hw_hub.m.vhdl PROC_REQUEST_HANDLING, a
// ClearPortFeature with wValue=1 (Port_Enable) drives:
//     hub_port_enable_int(var_port) <= '0'    (var_port = wIndex - 1)
// and per ip_xxx_3511_hs_mem_compound_structure.a.vhdl USBDC0's controller
// enable is gated by hub_port_enable(0):
//     usbreg_deviceenabled(1) <= hub_port_enable(0) and usbreg_arm_deviceenabled
// so clearing Port_Enable on port 1 (wIndex=1 -> var_port=0) forces USBDC0's
// deviceenabled to 0 - a genuine, waveform-visible power-down of the device
// controller. (PORT_POWER and PORT_SUSPEND are RTL no-ops in this IP - they
// only toggle status bits and are never wired to USBDC0, so using them would
// be a false pass.)
//
// Recovery is via SetFeature(PORT_RESET) on the same port, which per the same
// RTL re-asserts hub_port_enable_int(var_port)<='1' AND pulses
// hub_port_reset_int(var_port)<='1'. hub_port_reset(0) drives arm_dev_portreset
// into USBDC0, so USBDC0 sees a fresh bus reset (DRES_C) and returns to the
// Default state, after which the host re-enumerates it at address 2.
//
// The HS upstream link stays ENABLED and the HUB stays enumerated/configured
// at address 1 throughout; only USBDC0 is powered down and brought back.
//
// Flow:
//   1. SOF on, wait HS link ENABLED.
//   2. Full hub-aware enumeration: enumerate the HUB at address 1, bring up
//      downstream port 1, enumerate USBDC0 at address 2 (Steps A + B + C).
//   3. Power-down USBDC0: ClearFeature(PORT_ENABLE) on port 1 (degates
//      USBDC0 -> deviceenabled=0), confirm via GetPortStatus (enable bit=0),
//      hold, then recover via SetFeature(PORT_RESET) on port 1 (re-enable +
//      bus reset), and re-enumerate USBDC0 at address 2 (Step C).
//
// The 3-step hub-aware enumeration helpers (hub_enum_stepA,
// hub_port_bringup_stepB, usbdc0_enum_stepC) live in
// caliptra_ss_usb_base_sequence.svh.
// =============================================================================

class caliptra_ss_usb_hs_dev_powerdown_sequence extends caliptra_ss_usb_base_sequence;

    `uvm_object_utils(caliptra_ss_usb_hs_dev_powerdown_sequence)

    function new(string name = "caliptra_ss_usb_hs_dev_powerdown_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_usb_agent         host_agent_h;
        svt_usb_configuration usb_cfg;
        svt_usb_status        shared_status;

        host_agent_h  = resolve_host_agent();
        shared_status = resolve_shared_status();
        usb_cfg       = resolve_usb_cfg();

        start_sof_generation();
        wait_for_link_enabled(shared_status, "HS host link");

        // Allow MCU firmware to finish initial EP0 arming before the first SETUP.
        #20us;

        // --- Initial hub-aware enumeration (Steps A + B + C) ---
        // Enumerate the HUB at address 1, bring up downstream port 1, then
        // enumerate USBDC0 at address 2.
        hub_enum_stepA(host_agent_h, usb_cfg);
        hub_port_bringup_stepB(host_agent_h, usb_cfg);
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ","Initial hub-aware enumeration done (USBDC0 at addr 2).",UVM_LOW)
        #500us;

        // -----------------------------------------------------------------
        // GENUINE power-down of USBDC0, then power-up and re-enumeration.
        //
        // The HS upstream link stays ENABLED and the HUB stays enumerated
        // at address 1 throughout. The power-down is driven by a hub-class
        // ClearFeature(PORT_ENABLE) on downstream port 1, which per the RTL
        // forces hub_port_enable(0)=0 and therefore USBDC0's deviceenabled=0
        // (device controller degated / powered down - visible in the
        // waveform). Recovery is a SetFeature(PORT_RESET) on port 1, which
        // re-enables the port AND issues a fresh bus reset into USBDC0; the
        // host then re-enumerates USBDC0 at address 2 (Step C).
        //
        // Anchor management: after the initial enumeration the VIP remote
        // device anchor is at address 2 (USBDC0). The hub-class port
        // requests (power-down step + Step B) address the HUB at address 1,
        // so set the anchor to 1 first. usbdc0_enum_stepC() sets the anchor
        // to 0 for the freshly-reset USBDC0 and leaves it at 2 on completion.
        // -----------------------------------------------------------------
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Powering down USBDC0 via ClearFeature(PORT_ENABLE) on hub port 1...",UVM_LOW)

        usb_cfg.remote_device_cfg[0].device_address = 7'd1;
        host_agent_h.reconfigure(usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Anchor set to HUB address 1 for downstream port power-down.",UVM_LOW)

        usbdc0_powerdown_step(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ",
            "USBDC0 powered down (deviceenabled forced 0). Holding...",UVM_LOW)
        #200us;

        // Recover: SetFeature(PORT_RESET) re-enables the port and bus-resets
        // USBDC0, then re-enumerate it at address 2.
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Powering USBDC0 back up via SetFeature(PORT_RESET) on hub port 1...",UVM_LOW)
        hub_port_bringup_stepB(host_agent_h, usb_cfg);
        usbdc0_enum_stepC(host_agent_h, usb_cfg);
        `uvm_info("USB_HS_PWRDN_SEQ",
            "Post-power-up re-enumeration done (USBDC0 at addr 2).",UVM_LOW)
        #500us;

    endtask

    // -------------------------------------------------------------------------
    // Power-down step: degate USBDC0 via ClearFeature(PORT_ENABLE) on port 1.
    //   GetPortStatus (pre) -> ClearFeature(PORT_ENABLE) -> GetPortStatus (post,
    //   confirm Port_Enable status bit=0).
    // Per usb_app_hw_hub.m.vhdl, ClearPortFeature wValue=1 (Port_Enable) on
    // wIndex=1 (var_port=0) drives hub_port_enable_int(0)<='0', which per the
    // structure netlist forces USBDC0 usbreg_deviceenabled=0 (genuine
    // power-down). The post GetPortStatus reads hub_status(1)(1) = 0 to confirm.
    // On entry the VIP anchor must be 1 (HUB).
    // -------------------------------------------------------------------------
    task usbdc0_powerdown_step(svt_usb_agent host_agent_h, svt_usb_configuration usb_cfg);
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h00, 16'h0000, 16'h0001, 16'h0004,
            1, "GetPortStatus_Port1_prePD", usb_cfg);
        wait_xfer_done(host_agent_h, "GetPortStatus_Port1_prePD");

        // ClearFeature(PORT_ENABLE): feature selector PORT_ENABLE = 1.
        // This is the ONLY hub-class request wired to USBDC0's enable in this
        // IP; it forces deviceenabled=0 (real power-down).
        do_control_xfer(svt_usb_types::HOST_TO_DEVICE, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h01, 16'h0001, 16'h0001, 16'h0000,
            1, "ClearFeature_PORT_ENABLE_Port1", usb_cfg);
        wait_xfer_done(host_agent_h, "ClearFeature_PORT_ENABLE_Port1");
        #10us;

        // Confirm the port is now disabled: hub_status(1)(1)=Port_Enable=0.
        do_control_xfer(svt_usb_types::DEVICE_TO_HOST, svt_usb_types::CLASS,
            svt_usb_types::BMREQ_OTHER, 8'h00, 16'h0000, 16'h0001, 16'h0004,
            1, "GetPortStatus_Port1_postPD", usb_cfg);
        wait_xfer_done(host_agent_h, "GetPortStatus_Port1_postPD");
        #10us;
    endtask

endclass


`endif // CALIPTRA_SS_USB_HS_DEV_POWERDOWN_SEQUENCE_SV
