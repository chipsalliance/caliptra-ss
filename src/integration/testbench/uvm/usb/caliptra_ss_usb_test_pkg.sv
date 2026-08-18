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
  localparam int USB_PKG_VERSION = 224;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_usb_uvm_pkg::*;
  import caliptra_ss_usb_common_pkg::*;
  import caliptra_ss_usb_ocp_recovery_tb_pkg::*;
 

  `include "caliptra_ss_usb_shared_cfg.svh"
  `include "caliptra_ss_usb_env.svh"
  `include "caliptra_ss_usb_base_sequence.svh"
  `include "caliptra_ss_usb_init_sequence.svh"
  `include "caliptra_ss_usb_ocp_recovery_base_sequence.svh"
  `include "caliptra_ss_usb_nak_monitor_callback.svh"
  `include "caliptra_ss_usb_ocp_arbiter_packet_callback.svh"
  `include "caliptra_ss_usb_ocp_arbiter_checker.svh"
  `include "caliptra_ss_usb_ocp_post_sync_arbiter_base_sequence.svh"
  `include "caliptra_ss_usb_ocp_fifo_flow_control_sequence.svh"
  `include "caliptra_ss_usb_ocp_recovery_sequence.svh"
  `include "caliptra_ss_usb_ocp_fifo_ring_sequence.svh"
  `include "caliptra_ss_usb_ocp_cmd_handling_sequence.svh"
  `include "caliptra_ss_usb_ocp_device_status_access_semantics_sequence.svh"
  `include "caliptra_ss_usb_ocp_w1dc_access_semantics_sequence.svh"
  `include "caliptra_ss_usb_ocp_recovery_activation_access_semantics_sequence.svh"
  `include "caliptra_ss_usb_ocp_scoreboard.svh"
  `include "caliptra_ss_usb_ocp_recovery_env.svh"
  `include "caliptra_ss_usb_base_test.svh"
  `include "caliptra_ss_usb_basic_utmi_test.svh"
  `include "caliptra_ss_usb_ocp_recovery_test.svh"
  `include "caliptra_ss_usb_ocp_fifo_ring_test.svh"
  `include "caliptra_ss_usb_ocp_cmd_handling_test.svh"
  `include "caliptra_ss_usb_ocp_fifo_flow_control_test.svh"
  `include "caliptra_ss_usb_ocp_fifo_flow_indices_test.svh"
  `include "caliptra_ss_usb_ocp_fifo_flow_status_flags_test.svh"
  `include "caliptra_ss_usb_ocp_fifo_flow_usb_nak_test.svh"
  `include "caliptra_ss_usb_ocp_device_status_access_semantics_test.svh"
  `include "caliptra_ss_usb_ocp_w1dc_access_semantics_test.svh"
  `include "caliptra_ss_usb_ocp_recovery_activation_access_semantics_test.svh"
  `include "caliptra_ss_usb_ocp_arbiter_test.svh"

endpackage
