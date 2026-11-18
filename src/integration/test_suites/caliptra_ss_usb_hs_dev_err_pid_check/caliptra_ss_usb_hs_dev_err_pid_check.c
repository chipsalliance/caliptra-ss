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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_pid_check.
//
// Coverage target: usb_transfer_outcome_cg.cp_errortype bin pid_encoding (0x1),
// assigned at usb_pie.m.vhdl, four sites.
//
// The whole firmware body is shared with the other wire-corruption error
// tests and lives in libs/usb/usb_err_inject_fw_common.h - see that file for
// why the data check of caliptra_ss_usb_hs_dev_bulk_out.c is deliberately
// absent and why EP1 OUT is re-armed on every completion. This file only
// names the scenario for the log banner.
//
// The corruption itself is injected by the HOST, in
// caliptra_ss_usb_hs_dev_err_pid_sequence with pid_error_kind = PID_CHECK_ERROR. Nothing in this firmware
// is aware of it: the device is expected to detect the error on its own,
// which is exactly what the coverage bin records.

#define USB_ERR_INJECT_TEST_NAME "PID check-field corruption"
#include "usb_err_inject_fw_common.h"

// File contains AI-generated response based on internal company sources
