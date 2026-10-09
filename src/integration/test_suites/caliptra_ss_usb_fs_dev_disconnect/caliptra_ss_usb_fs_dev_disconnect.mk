# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Per-test makefile fragment, pulled in by tools/scripts/Makefile through
# "-include $(TEST_DIR)/$(TESTNAME).mk". It is read only when
# TESTNAME=caliptra_ss_usb_fs_dev_disconnect, so it cannot affect any other
# test.
#
# Enables caliptra_ss_mcu_console_fail_checker.sv, which turns any MCU
# console line containing FAIL into a UVM_ERROR. Without it a firmware
# failure such as "MCU: FAIL - enumeration timeout (got 0 of 3)" only
# printed to mcu_console.log and the run still reported TESTCASE PASSED,
# because firmware signals failure by halting, exactly as it does on
# success. The "=1" form is kept for consistency with the test yml;
# $test$plusargs matches on prefix, so the value itself is ignored.
VCS_SIM_OPTS += +mcu_console_fail_check=1

# No VBus plusargs are needed. VIP-owned VBus is the unconditional testbench
# default: caliptra_ss_top_tb.sv leaves utmi_dut_mac_if.VbusValid undriven so
# the Synopsys VIP physical layer is its only driver, and
# caliptra_ss_usb_vbus_driver.sv always forwards the resolved value to the DUT
# cptra_ss_usb_USB_VBus_i / cptra_ss_usb_sessend_i pins. See
# docs/usb_vip_vbus_ownership.md.
