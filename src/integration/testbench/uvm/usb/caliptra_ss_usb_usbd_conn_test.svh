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
class caliptra_ss_usb_usbd_conn_test extends caliptra_ss_usb_base_test;
  `uvm_component_utils(caliptra_ss_usb_usbd_conn_test)

  function new(string name = "caliptra_ss_usb_usbd_conn_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // FS mode: disable HS capability, force FS speed on host and device.
    cfg.host_cfg.local_host_cfg.high_speed_capable = 0;
    cfg.host_cfg.speed = svt_usb_types::FS;
    cfg.dev_cfg.speed = svt_usb_types::FS;
    cfg.dev_cfg.local_device_cfg[0].connected_bus_speed = svt_usb_types::FS;
    cfg.dev_cfg.local_device_cfg[0].functionality_support = svt_usb_types::FS;
    cfg.dev_cfg.local_device_cfg[0].device_timeout = 5000us;
    // Align endpoint speeds to FS to satisfy is_valid() - base class sets HS.
    cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].speed = svt_usb_types::FS;
    cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[0].max_packet_size = `SVT_USB_FS_CONTROL_MAX_PACKET_SIZE;
    cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].speed = svt_usb_types::FS;
    cfg.dev_cfg.local_device_cfg[0].endpoint_cfg[1].max_packet_size = `SVT_USB_FS_BULK_MAX_PACKET_SIZE;
    // Register sequence on per-agent virtual sequencer to avoid p_sequencer
    // cast failure (uvm_declare_p_sequencer(svt_usb_virtual_sequencer)).
    uvm_config_db#(uvm_object_wrapper)::set(this,
        "env.host_agent.virt_sequencer.main_phase", "default_sequence",
        caliptra_ss_usb_usbd_conn_sequence::type_id::get());
  endfunction

endclass
