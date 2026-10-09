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
# TESTNAME=caliptra_ss_usb_dual_device_fs_bulk_loopback, so it cannot affect
# any other test.
#
# This fragment is the enablement path for the plain Makefile flow, i.e.
#
#   make -f $CALIPTRA_SS_ROOT/tools/scripts/Makefile \
#        TESTNAME=caliptra_ss_usb_dual_device_fs_bulk_loopback \
#        CALIPTRA_TESTNAME=cptra_bringup CALIPTRA_AUX=soc_ifc_ss \
#        CALIPTRA_SS_CLK_FREQ=400 vcs
#
# Everything the test needs (firmware define + runtime plusargs) is set here,
# so no extra command-line switches are required. The companion
# caliptra_ss_usb_dual_device_fs_bulk_loopback.yml carries the same settings
# for the yml-driven flow (run_caliptra_test.py); the two are intentionally
# redundant and must be kept in sync.
#
# ---------------------------------------------------------------------------
# 1. Firmware (C) compile define
# ---------------------------------------------------------------------------
# This is a DUAL-DEVICE image: it drives BOTH the USBDC0 (0x2000_0000 /
# 0x3000_0000) and USBDC1 (0x2000_2000 / 0x3001_0000) apertures, so it must
# NOT be built with -DUSB_DEV_SEL=1 (that would compile-time pin the shared
# USB library to a single controller). -DUSB_HUB_COMPOUND_DEV1_IRQ makes
# init_usb_interrupts() enable PIC vector 6 and makes mcu_isr.h compile in
# service_usb_dev1_intr(). BUILD_CFLAGS reaches gcc via TEST_CFLAGS; this
# fragment is included after TEST_CFLAGS is defined, but TEST_CFLAGS is a
# recursive variable, so appending here still takes effect.
BUILD_CFLAGS += -DUSB_HUB_COMPOUND_DEV1_IRQ

# ---------------------------------------------------------------------------
# 2. Runtime plusargs
# ---------------------------------------------------------------------------
# All testbench-side enables are RUNTIME plusargs checked with
# $test$plusargs(), not compile-time `ifdefs, so one simv image is reusable
# across every test. The "=1" form is used throughout for consistency with
# the yml: run_caliptra_test.py only forwards plusargs matching +NAME=VALUE,
# and $test$plusargs() matches on the NAME prefix, so the value is ignored.

# UVM test to run.
VCS_SIM_OPTS += +UVM_TESTNAME=caliptra_ss_usb_dual_device_fs_bulk_loopback_test

# Activates the testbench loopback that ORs cptra_ss_usb_dev1_irq_o onto
# cptra_ss_mcu_ext_int[6] in caliptra_ss_top_tb.sv. The loopback is always
# compiled in and is gated only by this plusarg.
VCS_SIM_OPTS += +USB_HUB_COMPOUND_DEV1_IRQ=1

# Arms caliptra_ss_usb_fs_speed_checker.sv, which is instantiated in
# caliptra_ss_top_tb.sv but stays inert unless this plusarg is present. The
# checker observes the UTMI interface and proves the link really is running at
# Full Speed rather than High Speed:
#   CHK_XCVR_FS     requires XcvrSelect=1 and TermSelect=1 on the first packet
#                   (both would be 0 if the chirp handshake had reached HS);
#   CHK_RATE_FS     measures the RXValid-to-RXValid byte period, which must be
#                   about 667 ns (12 Mbit/s) and not about 17 ns (480 Mbit/s);
#   CHK_SAW_TRAFFIC fails if no packet was ever seen, or if traffic started but
#                   not enough samples were collected to confirm the rate.
# The last check is released by the global uvm_event usb_fs_obs_window_done,
# which caliptra_ss_usb_dual_device_fs_bulk_loopback_sequence triggers once
# both loopbacks have completed.
#
# CHK_SOF_PERIOD (+usb_fs_sof_check) is deliberately NOT enabled: it needs
# several milliseconds of bus observation to time consecutive SOFs, which this
# test does not run long enough to provide. The XcvrSelect and byte-rate checks
# above already separate FS from HS unambiguously.
VCS_SIM_OPTS += +usb_fs_speed_check=1

# File contains AI-generated response based on internal company sources
