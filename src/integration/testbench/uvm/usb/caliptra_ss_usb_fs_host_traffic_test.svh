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

`ifndef CALIPTRA_SS_USB_FS_HOST_TRAFFIC_TEST_SV
`define CALIPTRA_SS_USB_FS_HOST_TRAFFIC_TEST_SV

// =============================================================================
// USB Full-Speed host traffic test.

// register writes (USBMODE, USBCMD, PORTSC1) and verified 256
// bytes of BULK OUT data received on EP1.
// This test:
//   - Forces the VIP to Full-Speed (no HS chirp) by clearing high_speed_capable
//     and setting speed=FS on both host and device configurations, replicating
//     the original PORTSC1_PFSC (Port Force Full Speed Connect) behavior.
//   - Configures EP1 as a BULK OUT endpoint at FS (max packet 64 bytes),
//     matching the original ENDPOINTCTRL1 / dQH setup in mem.txt (EP1 OUT,
//     MaxPacketLength=0x40, ZLT=ENABLE).
//   - Binds the host virtual sequencer to caliptra_ss_usb_fs_host_traffic_sequence
//     which enumerates the device and sends 256 bytes of incrementing bulk OUT
//     data to EP1. The MCU firmware verifies the data pattern.
// Usage:
//   +UVM_TESTNAME=caliptra_ss_usb_fs_host_traffic_test
// =============================================================================
class caliptra_ss_usb_fs_host_traffic_test extends caliptra_ss_usb_base_test;
    `uvm_component_utils(caliptra_ss_usb_fs_host_traffic_test)

    function new(string name = "caliptra_ss_usb_fs_host_traffic_test",
                 uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);

        // --- Force Full-Speed operation ---
        // high_speed_capable=0: suppresses HS chirp so the link attaches at FS.
        cfg.host_cfg.local_host_cfg.high_speed_capable = 1'b0;

        // Set host_cfg.speed=FS so the VIP host stack uses direct FS token
        // protocol (SETUP/IN/OUT/ACK) instead of HS split transactions
        // (SSPLIT/CSPLIT). Without this, a HS host talking to a FS device
        // uses split transactions as if there is a TT hub between them, but
        // the DUT is directly connected via UTMI - there is no hub. This was
        // causing `valid_device_response_check_Dev1_EP1_OUT: NYET to SSPLIT`
        // errors and EP0 timeouts because the DUT does not understand SSPLIT.
        cfg.host_cfg.speed = svt_usb_types::FS;

        // Set dev_cfg speed fields to FS so dev_cfg.is_valid() accepts the
        // 64-byte FS packet sizes (HS bulk requires 512 bytes).
        cfg.dev_cfg.speed                                            = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].connected_bus_speed         = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].functionality_support       = svt_usb_types::FS;

        // Increase device_timeout to give MCU firmware time to process SETUP
        // packets and prime EP0 IN/OUT buffers.  With the VIP scaledown factor
        // (~150x), real-time 500 us maps to only ~3.3 us sim time, which is
        // less than the ~5 us sim time the MCU interrupt handler needs to
        // prepare and post an IN response, causing repeated
        // `device_response_timeout_check` UVM_ERRORs on every control transfer.
        // Setting 5 ms gives ~33 us sim window, comfortably above MCU latency.
        cfg.dev_cfg.local_device_cfg[0].device_timeout              = 5000us;

        // EP0: CONTROL at FS, 64-byte max packet.
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;

        // EP1: BULK OUT at FS, 64-byte max packet.
        // Matches original mem.txt dQH: EndPoint=1, Direction=OUT,
        // MaxPacketLength=0x40 (64 bytes), ZeroLengthTermination=ENABLE.
        // Matches ENDPOINTCTRL1 write: 0x00880088 (EP1 OUT bulk enabled).
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].direction       = svt_usb_types::OUT;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed           = svt_usb_types::FS;
        cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_FS_BULK_MAX_PACKET_SIZE;

        // Bind the host virtual sequencer to the FS host traffic sequence.
        uvm_config_db#(uvm_object_wrapper)::set(this,
            "env.host_agent.virt_sequencer.main_phase", "default_sequence",
            caliptra_ss_usb_fs_host_traffic_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction

endclass

`endif // CALIPTRA_SS_USB_FS_HOST_TRAFFIC_TEST_SV
