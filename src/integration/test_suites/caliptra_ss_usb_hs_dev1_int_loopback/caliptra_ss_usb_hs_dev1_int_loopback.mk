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
# TESTNAME=caliptra_ss_usb_hs_dev1_int_loopback, so it cannot affect any other test.
#
# This fragment is the enablement path for the plain Makefile flow, i.e.
#
#   make -f $CALIPTRA_SS_ROOT/tools/scripts/Makefile \
#        TESTNAME=caliptra_ss_usb_hs_dev1_int_loopback \
#        CALIPTRA_TESTNAME=cptra_bringup CALIPTRA_AUX=soc_ifc_ss \
#        CALIPTRA_SS_CLK_FREQ=400 vcs
#
# The companion caliptra_ss_usb_hs_dev1_int_loopback.yml carries the same
# settings for the yml-driven flow (run_caliptra_test.py); the two are
# intentionally redundant and must be kept in sync.
#
# ---------------------------------------------------------------------------
# 1. Firmware (C) compile define
# ---------------------------------------------------------------------------
# This is a SINGLE-controller USBDC1 image. -DUSB_DEV_SEL=1 pins the shared
# USB library (libs/usb/usb.h, usb.c) to the USBDC1 aperture (CSR
# 0x2000_2000, MEM 0x3001_0000) at compile time, so every USB_DEV_* macro in
# the firmware resolves to device1.
#
# -DUSB_HUB_COMPOUND_DEV1_IRQ is deliberately NOT set: this test drives
# USBDC1 by POLLING and never enables PIC vector 6, so no interrupt mailbox
# is involved and the vector 3 / USB_DEV_SEL aliasing hazard that affects the
# interrupt-driven dev1 tests does not apply here.
#
# BUILD_CFLAGS reaches gcc via TEST_CFLAGS; this fragment is included after
# TEST_CFLAGS is defined, but TEST_CFLAGS is a recursive variable, so
# appending here still takes effect.
BUILD_CFLAGS += -DUSB_DEV_SEL=1

# ---------------------------------------------------------------------------
# 2. Runtime plusargs
# ---------------------------------------------------------------------------
# All testbench-side enables are RUNTIME plusargs checked with
# $test$plusargs(), not compile-time `ifdefs, so one simv image is reusable
# across every test.

# UVM test to run. No other plusargs are needed.
VCS_SIM_OPTS += +UVM_TESTNAME=caliptra_ss_usb_hs_dev1_int_loopback_test
