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
# "-include $(TEST_DIR)/$(TESTNAME).mk" (line 94). It is read only when
# TESTNAME=caliptra_ss_usb_dual_device_hs_dev0_hotplug, so it cannot affect
# any other test.
#
# This fragment is the enablement path for the plain Makefile flow, i.e.
#
#   make -f $CALIPTRA_SS_ROOT/tools/scripts/Makefile \
#        TESTNAME=caliptra_ss_usb_dual_device_hs_dev0_hotplug \
#        CALIPTRA_TESTNAME=cptra_bringup CALIPTRA_AUX=soc_ifc_ss \
#        CALIPTRA_SS_CLK_FREQ=400 vcs
#
# The companion caliptra_ss_usb_dual_device_hs_dev0_hotplug.yml carries the
# same settings for the yml-driven flow (run_caliptra_test.py); the two are
# intentionally redundant and must be kept in sync.

# ---------------------------------------------------------------------------
# 1. Firmware (C) compile define
# ---------------------------------------------------------------------------
# This is a DUAL-DEVICE image: a single binary drives BOTH USBDC0 (hub port 1)
# and USBDC1 (hub port 2), so it must NOT be built with -DUSB_DEV_SEL=1, which
# would compile-time pin the shared USB library to one controller. The active
# controller is selected at runtime with usb_select_device().
# -DUSB_HUB_COMPOUND_DEV1_IRQ makes init_usb_interrupts() enable PIC vector 6
# and makes mcu_isr.h compile in service_usb_dev1_intr(). BUILD_CFLAGS reaches
# gcc via TEST_CFLAGS; this fragment is included after TEST_CFLAGS is defined,
# but TEST_CFLAGS is a recursive variable, so appending here still takes
# effect.
BUILD_CFLAGS += -DUSB_HUB_COMPOUND_DEV1_IRQ

# ---------------------------------------------------------------------------
# 2. USB VIP compile-time define: device debug port depth
# ---------------------------------------------------------------------------
# This one is a COMPILE-time define, not a runtime plusarg, and it cannot be
# anything else. SVT_USB_MAX_DEVICE_DEBUG_PORT sizes two static VIP interface
# arrays that are elaborated before time 0:
#
#   svt_usb_ess_protocol_block_debug_if.svi:23
#     svt_usb_ess_protocol_device_debug_if
#         usb_ess_protocol_device_debug_if[`SVT_USB_MAX_DEVICE_DEBUG_PORT]();
#   svt_usb_ess_status_debug_if.svi:11
#     svt_usb_ess_device_status_debug_if
#         usb_ess_device_status_debug_if[`SVT_USB_MAX_DEVICE_DEBUG_PORT]();
#
# An array bound must be constant at elaboration, so no $test$plusargs form of
# this control exists.
#
# The VIP default is 3, declared as
#   `SVT_REPLACEABLE_DEFINE(SVT_USB_MAX_DEVICE_DEBUG_PORT,3)
# in svt_usb_common_defines.svi:6893. Being "replaceable" is what makes a
# command-line +define+ override legal rather than a VIP source edit.
#
# get_protocol_device_debug_if() guards with "index >= MAX" and, when the
# bound is exceeded, prints
#   "Debug Port is supported for 3 devices. To increase number of devices in
#    debug port set define SVT_USB_MAX_DEVICE_DEBUG_PORT."
# and calls $finish (svt_usb_ess_protocol_block_debug_if.svi:32-34).
#
# This test ends up with a remote_device_cfg[] queue of depth FOUR, which is
# one past the default bound, so the guard fired and killed the simulation at
# time 0 before any USB traffic. Note the depth tracks distinct bus ADDRESSES
# in play, not the number of devices - there are only three devices:
#
#   slot 0 = address 0  default address, pre-SET_ADDRESS (NOT a device; this
#                       slot already exists, created by the shared-cfg
#                       constructor, and is the stage every device answers on
#                       after a hub port reset)
#   slot 1 = address 1  hub
#   slot 2 = address 2  USBDC0
#   slot 3 = address 3  USBDC1
#
# caliptra_ss_usb_dual_device_hs_dev0_hotplug_test.svh calls
# add_remote_device_slot() three times, for slots 1-3; slot 0 is inherited.
# Keeping address 0 in its own permanently reserved slot is what lets every
# slot's device_address be write-once at build_phase, so no live slot is ever
# retargeted and reconfigure() is never called after bring-up. That invariant
# is the fix for the bulk endpoint data-toggle reset; see the commit message
# on caliptra_ss_usb_shared_cfg.svh for the measured PID evidence.
#
# The value is set to 8 to leave headroom for further multi-device tests.
# VCS_COMP_OPTS is consumed by the vlogan command in tools/scripts/Makefile
# (line 533-534), which is the step that analyses the VIP .svi files, so an
# append here reaches the right tool invocation.
VCS_COMP_OPTS += +define+SVT_USB_MAX_DEVICE_DEBUG_PORT=8

# ---------------------------------------------------------------------------
# 3. Runtime plusargs
# ---------------------------------------------------------------------------
# Unlike the define above, every testbench-side enable below is a RUNTIME
# plusarg checked with $test$plusargs(), so one simv image stays reusable. The
# "=1" form is used for consistency with the yml: run_caliptra_test.py only
# forwards plusargs matching +NAME=VALUE, and $test$plusargs() matches on the
# NAME prefix, so the value itself is ignored.

# UVM test to run.
VCS_SIM_OPTS += +UVM_TESTNAME=caliptra_ss_usb_dual_device_hs_dev0_hotplug_test

# Activates the testbench loopback that ORs cptra_ss_usb_dev1_irq_o onto
# cptra_ss_mcu_ext_int[6] in caliptra_ss_top_tb.sv. The loopback is always
# compiled in and is gated only by this plusarg. It is the testbench half of
# the pair whose firmware half is -DUSB_HUB_COMPOUND_DEV1_IRQ above; both are
# required for the MCU to service DEV1 interrupts.
VCS_SIM_OPTS += +USB_HUB_COMPOUND_DEV1_IRQ=1
