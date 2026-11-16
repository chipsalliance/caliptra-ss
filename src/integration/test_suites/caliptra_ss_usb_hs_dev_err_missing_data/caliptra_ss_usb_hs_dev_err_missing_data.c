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
// Description: MCU firmware for caliptra_ss_usb_hs_dev_err_missing_data.
//
// Coverage target: usb_transfer_outcome_cg.cp_errortype bin timeout (0x6),
// assigned at usb_pie.m.vhdl line 2442 (OUT/SETUP token accepted, no DATA
// packet before the packet-handling timer expires).
//
// The whole firmware body is shared with the other wire-corruption/sequencing
// error tests and lives in libs/usb/usb_err_inject_fw_common.h: EP1 OUT is
// kept armed and re-armed on every completion, with no data check (a
// mismatch or a missing transfer altogether is the point of this family).
//
// The stimulus itself - a lone OUT token with no following DATA packet - is
// driven by the HOST, in caliptra_ss_usb_hs_dev_err_missing_data_sequence.
// Nothing in this firmware is aware of it; it simply never sees the EP1 OUT
// completion interrupt for that one token and keeps polling.

#define USB_ERR_INJECT_TEST_NAME "missing DATA packet after OUT token"
#include "usb_err_inject_fw_common.h"

// File contains AI-generated response based on internal company sources
