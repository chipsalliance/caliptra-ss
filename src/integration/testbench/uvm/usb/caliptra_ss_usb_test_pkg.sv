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
//

package caliptra_ss_usb_test_pkg;

  // Force VCS recompile when USB UVM package contents change.
  localparam int USB_PKG_VERSION = 146;





  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_usb_uvm_pkg::*;

  `include "caliptra_ss_usb_data_check_api.svh"
  `include "caliptra_ss_usb_data_check_api_impl.svh"

  `include "caliptra_ss_usb_shared_cfg.svh"
  `include "caliptra_ss_usb_env.svh"
  `include "caliptra_ss_usb_base_sequence.svh"
  `include "caliptra_ss_usb_init_sequence.svh"
  `include "caliptra_ss_usb_get_status_sequence.svh"
  `include "caliptra_ss_usb_hub_qualifier_sequence.svh"
  `include "caliptra_ss_usb_hub_config_descriptor_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_hub_config_descriptor_sequence.svh"
  `include "caliptra_ss_usb_get_hub_status_sequence.svh"
  `include "caliptra_ss_usb_get_hub_descriptor_sequence.svh"

  `include "caliptra_ss_usb_get_device_descriptor_sequence.svh"

  `include "caliptra_ss_usb_base_test.svh"
  `include "caliptra_ss_usb_basic_utmi_test.svh"

  // FS testcases (pre-existing)
  `include "caliptra_ss_usb_fs_clock_sequence.svh"
  `include "caliptra_ss_usb_fs_clock_test.svh"
  `include "caliptra_ss_usb_fs_host_traffic_sequence.svh"
  `include "caliptra_ss_usb_fs_host_traffic_test.svh"

  // HS testcases
  `include "caliptra_ss_usb_hs_conn_sequence.svh"
  `include "caliptra_ss_usb_hs_conn_test.svh"
  `include "caliptra_ss_usb_hs_dev_bulk_out_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_bulk_out_test.svh"
  `include "caliptra_ss_usb_hs_dev_disconnect_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_disconnect_test.svh"
  `include "caliptra_ss_usb_hs_dev_nbyte_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_nbyte_test.svh"
  `include "caliptra_ss_usb_hs_dev_hub_port_suspend_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_hub_port_suspend_test.svh"
  `include "caliptra_ss_usb_hs_dev_powerdown_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_powerdown_test.svh"
  `include "caliptra_ss_usb_hs_dev_global_suspend_L2_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_global_suspend_L2_test.svh"
  `include "caliptra_ss_usb_hs_dev_lpm_l1_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_lpm_l1_test.svh"
  `include "caliptra_ss_usb_hs_dev_resume_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_resume_test.svh"
//  `include "caliptra_ss_usb_hs_dev_ctrl_ep_sequence.svh"
//  `include "caliptra_ss_usb_hs_dev_ctrl_ep_test.svh"
//  `include "caliptra_ss_usb_hs_dev_sof_sequence.svh"
//  `include "caliptra_ss_usb_hs_dev_sof_test.svh"
  `include "caliptra_ss_usb_hs_dev_iso_out_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_iso_out_test.svh"
  `include "caliptra_ss_usb_hs_host_bulk_out_sequence.svh"
  `include "caliptra_ss_usb_hs_host_bulk_out_test.svh"
  `include "caliptra_ss_usb_hs_host_iso_out_sequence.svh"
  `include "caliptra_ss_usb_hs_host_iso_out_test.svh"
//  `include "caliptra_ss_usb_hs_host_powerdown_sequence.svh"
//  `include "caliptra_ss_usb_hs_host_powerdown_test.svh"
//  `include "caliptra_ss_usb_hs_host_remotewakeup_sequence.svh"
//  `include "caliptra_ss_usb_hs_host_remotewakeup_test.svh"
//  `include "caliptra_ss_usb_hs_host_resume_sequence.svh"
//  `include "caliptra_ss_usb_hs_host_resume_test.svh"

  // FS additional testcases
  `include "caliptra_ss_usb_fs_dev_bulk_loopback_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_bulk_loopback_test.svh"
  `include "caliptra_ss_usb_fs_dev_disconnect_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_disconnect_test.svh"
//  `include "caliptra_ss_usb_fs_host_intnak_sequence.svh"
//  `include "caliptra_ss_usb_fs_host_intnak_test.svh"
//  `include "caliptra_ss_usb_fs_host_remotewakeup_sequence.svh"
//  `include "caliptra_ss_usb_fs_host_remotewakeup_test.svh"
  // Re-enabled: both the sequence and the firmware were rewritten to actually
  // test device-initiated remote wakeup (the sequence now waits on
  // svt_usb_status::device_remote_wakeup_in_progress instead of driving an
  // unconditional host resume after a fixed delay). See the test README.
  `include "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_sequence.svh"
  `include "caliptra_ss_usb_fs_host_remotewakeup_fromdevice_test.svh"
//  `include "caliptra_ss_usb_fs_idau_sec_level_sequence.svh"
//  `include "caliptra_ss_usb_fs_idau_sec_level_test.svh"
//  `include "caliptra_ss_usb_fs_root2_sequence.svh"
//  `include "caliptra_ss_usb_fs_root2_test.svh"

  // ACC-generated FS<->HS counterpart testcases (ported with acc)
  `include "caliptra_ss_usb_hs_clock_sequence.svh"
  `include "caliptra_ss_usb_hs_clock_test.svh"
  `include "caliptra_ss_usb_hs_dev_bulk_loopback_sequence.svh"
  `include "caliptra_ss_usb_hs_dev_bulk_loopback_test.svh"
  `include "caliptra_ss_usb_fs_conn_sequence.svh"
  `include "caliptra_ss_usb_fs_conn_test.svh"
  `include "caliptra_ss_usb_fs_dev_bulk_out_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_bulk_out_test.svh"
  `include "caliptra_ss_usb_fs_dev_iso_out_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_iso_out_test.svh"
  `include "caliptra_ss_usb_fs_dev_nbyte_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_nbyte_test.svh"
  `include "caliptra_ss_usb_fs_dev_powerdown_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_powerdown_test.svh"
  `include "caliptra_ss_usb_fs_dev_global_suspend_L2_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_global_suspend_L2_test.svh"
  `include "caliptra_ss_usb_fs_dev_resume_sequence.svh"
  `include "caliptra_ss_usb_fs_dev_resume_test.svh"

  // USBDC1 (device1) replicated testcases. Same scenarios as the USBDC0
  // families above, but the host brings up hub downstream port 2 and the
  // firmware is built with -DUSB_DEV_SEL=1 so the shared USB library targets
  // the USBDC1 aperture at 0x2001_0000. Generated by
  // tools/scripts/gen_usb_dev_variants.py.
  `include "caliptra_ss_usb_hs_dev1_bulk_out_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_bulk_out_test.svh"
  `include "caliptra_ss_usb_hs_dev1_nbyte_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_nbyte_test.svh"
  `include "caliptra_ss_usb_hs_dev1_iso_out_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_iso_out_test.svh"
  `include "caliptra_ss_usb_hs_dev1_bulk_loopback_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_bulk_loopback_test.svh"
  `include "caliptra_ss_usb_hs_dev1_disconnect_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_disconnect_test.svh"
  `include "caliptra_ss_usb_hs_dev1_powerdown_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_powerdown_test.svh"
  `include "caliptra_ss_usb_hs_dev1_global_suspend_L2_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_global_suspend_L2_test.svh"
  `include "caliptra_ss_usb_hs_dev1_resume_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_resume_test.svh"
  `include "caliptra_ss_usb_fs_dev1_bulk_loopback_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_bulk_loopback_test.svh"
  `include "caliptra_ss_usb_fs_dev1_bulk_out_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_bulk_out_test.svh"
  `include "caliptra_ss_usb_fs_dev1_disconnect_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_disconnect_test.svh"
  `include "caliptra_ss_usb_fs_dev1_iso_out_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_iso_out_test.svh"
  `include "caliptra_ss_usb_fs_dev1_nbyte_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_nbyte_test.svh"
  `include "caliptra_ss_usb_fs_dev1_powerdown_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_powerdown_test.svh"
  `include "caliptra_ss_usb_fs_dev1_global_suspend_L2_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_global_suspend_L2_test.svh"
  `include "caliptra_ss_usb_fs_dev1_resume_sequence.svh"
  `include "caliptra_ss_usb_fs_dev1_resume_test.svh"

  // USBDC1 (device1) bring-up / link-observation counterparts of the dev0
  // non-device tests. caliptra_ss_usb_dev1_init runs the full hub + USBDC1
  // enumeration; the other three only observe link bring-up while the
  // firmware drives USBDC1 (-DUSB_DEV_SEL=1). The dev1 init variant reuses
  // caliptra_ss_usb_port_reset_sequence from caliptra_ss_usb_init_sequence.svh
  // and therefore must be included after it.
  `include "caliptra_ss_usb_dev1_init_sequence.svh"
  `include "caliptra_ss_usb_dev1_init_test.svh"
  `include "caliptra_ss_usb_hs_dev1_clock_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_clock_test.svh"
  `include "caliptra_ss_usb_hs_dev1_conn_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_conn_test.svh"
  `include "caliptra_ss_usb_usbd1_conn_sequence.svh"
  `include "caliptra_ss_usb_usbd1_conn_test.svh"

  // USBD testcases
  `include "caliptra_ss_usb_usbd_conn_sequence.svh"
  `include "caliptra_ss_usb_usbd_conn_test.svh"

  // Device-status / qualifier testcases, split into three focused scenarios,
  // each with an HS and an FS variant:
  //   - get_status:     SetFeature/ClearFeature(DEVICE_REMOTE_WAKEUP)+GET_STATUS
  //                     for hub and dev0 (caliptra_ss_usb_get_status_sequence).
  //   - hub_qualifier:  GetDeviceQualifier for the hub
  //                     (caliptra_ss_usb_hub_qualifier_sequence).
  //   - get_hub_status: hub-class GetHubStatus
  //                     (caliptra_ss_usb_get_hub_status_sequence).
  //   - get_device_descriptor: standard GET_DESCRIPTOR(DEVICE) for hub and dev0
  //                     (caliptra_ss_usb_get_device_descriptor_sequence).
  `include "caliptra_ss_usb_hs_dev_get_status_test.svh"
  `include "caliptra_ss_usb_fs_dev_get_status_test.svh"
  `include "caliptra_ss_usb_hs_dev_hub_qualifier_test.svh"
  `include "caliptra_ss_usb_fs_dev_hub_qualifier_test.svh"
  `include "caliptra_ss_usb_hs_dev_get_hub_status_test.svh"
  `include "caliptra_ss_usb_fs_dev_get_hub_status_test.svh"
  `include "caliptra_ss_usb_hs_dev_get_hub_descriptor_test.svh"
  `include "caliptra_ss_usb_fs_dev_get_hub_descriptor_test.svh"
  // HS-only hub CONFIGURATION / OTHER_SPEED_CONFIGURATION descriptor check
  // (OTHER_SPEED_CONFIGURATION is defined only for HS-capable devices).
  `include "caliptra_ss_usb_hs_dev_hub_config_descriptor_test.svh"
  // FS variant: CONFIGURATION-only descriptor check (no OTHER_SPEED_CONFIG),
  // IRQ-driven MCU firmware.
  `include "caliptra_ss_usb_fs_dev_hub_config_descriptor_test.svh"

  `include "caliptra_ss_usb_hs_dev_get_device_descriptor_test.svh"
  `include "caliptra_ss_usb_fs_dev_get_device_descriptor_test.svh"

  // USBDC1 (device1) replicas of the four device-status / qualifier families
  // above. Each brings up hub downstream port 2 (USBDC1) and checks the
  // addressed device as "dev1"; the matching firmware is built with
  // -DUSB_DEV_SEL=1. These four families share a non-prefixed base sequence
  // for the dev0 variants, so the dev1 sequences are dedicated files (they
  // cannot be produced by gen_usb_dev_variants.py). Only HS variants are
  // provided (dev1-only Full Speed is not a supported configuration - see
  // claude_md/15_usb_dev1_replication.md section 8). Sequences must precede
  // their tests.
  `include "caliptra_ss_usb_hs_dev1_get_status_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_hub_qualifier_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_get_hub_status_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_get_device_descriptor_sequence.svh"
  `include "caliptra_ss_usb_hs_dev1_get_status_test.svh"
  `include "caliptra_ss_usb_hs_dev1_hub_qualifier_test.svh"
  `include "caliptra_ss_usb_hs_dev1_get_hub_status_test.svh"
  `include "caliptra_ss_usb_hs_dev1_get_device_descriptor_test.svh"


//  `include "caliptra_ss_usb_usbd_wakeup_sequence.svh"
//  `include "caliptra_ss_usb_usbd_wakeup_test.svh"
//  `include "caliptra_ss_usb_usbd_wakeup_fromdevice_sequence.svh"
//  `include "caliptra_ss_usb_usbd_wakeup_fromdevice_test.svh"

endpackage

// File contains AI-generated response based on internal company sources
