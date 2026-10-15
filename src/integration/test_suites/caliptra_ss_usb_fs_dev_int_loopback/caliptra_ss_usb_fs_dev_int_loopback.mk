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
# TESTNAME=caliptra_ss_usb_fs_dev_int_loopback, so it cannot affect any other test.
#
# This fragment is the enablement path for the plain Makefile flow, i.e.
#
#   make -f $CALIPTRA_SS_ROOT/tools/scripts/Makefile \
#        TESTNAME=caliptra_ss_usb_fs_dev_int_loopback \
#        CALIPTRA_TESTNAME=cptra_bringup CALIPTRA_AUX=soc_ifc_ss \
#        CALIPTRA_SS_CLK_FREQ=400 vcs
#
# The companion caliptra_ss_usb_fs_dev_int_loopback.yml carries the same
# settings for the yml-driven flow (run_caliptra_test.py); the two are
# intentionally redundant and must be kept in sync.
#
# ---------------------------------------------------------------------------
# 1. Firmware (C) compile defines
# ---------------------------------------------------------------------------
# None. This test targets USBDC0, which is what the shared USB library
# resolves to by default (USB_DEV_SEL defaults to 0 in libs/usb/usb.h), so no
# BUILD_CFLAGS are required. The Full Speed attach is driven entirely from the
# UVM test class, which overrides the VIP speed configuration; there is no
# firmware-visible FS/HS switch.

# ---------------------------------------------------------------------------
# 2. Runtime plusargs
# ---------------------------------------------------------------------------
# All testbench-side enables are RUNTIME plusargs checked with
# $test$plusargs(), not compile-time `ifdefs, so one simv image is reusable
# across every test.

# UVM test to run. No other plusargs are needed; in particular
# usb_suspend_resume_check is deliberately left off, matching the companion
# .yml.
VCS_SIM_OPTS += +UVM_TESTNAME=caliptra_ss_usb_fs_dev_int_loopback_test
