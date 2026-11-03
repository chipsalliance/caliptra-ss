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
# TESTNAME=caliptra_ss_usb_hs_dev1_hub_config_descriptor, so it cannot affect any other test.
#
# This fragment is the enablement path for the plain Makefile flow, i.e.
#
#   make -f $CALIPTRA_SS_ROOT/tools/scripts/Makefile \
#        TESTNAME=caliptra_ss_usb_hs_dev1_hub_config_descriptor \
#        CALIPTRA_TESTNAME=cptra_bringup CALIPTRA_AUX=soc_ifc_ss \
#        CALIPTRA_SS_CLK_FREQ=400 vcs
#
# The companion caliptra_ss_usb_hs_dev1_hub_config_descriptor.yml carries the same
# settings for the yml-driven flow (run_caliptra_test.py); the two are
# intentionally redundant and must be kept in sync.
#
# ---------------------------------------------------------------------------
# 1. Firmware (C) compile define
# ---------------------------------------------------------------------------
# -DUSB_HUB_COMPOUND_DEV1_IRQ makes init_usb_interrupts() enable PIC vector 6
# (USBDC1's looped IRQ) and makes mcu_isr.h compile in
# service_usb_dev1_intr() plus the mcu_intr_rcv.usb_dev1 mailbox field.
#
# -DUSB_DEV_SEL=1 is deliberately NOT set. service_usb_intr() is an inline
# function in mcu_isr.h that resolves USB_DEV_INTSTAT / USB_DEV_INTEN through
# the compile-time USB_DEV_SEL aliases, while PIC vector 3 is hard wired to
# USBDC0's usb_dev_irq in caliptra_ss_top.sv. Under -DUSB_DEV_SEL=1 that
# handler would read and write-1-to-clear USBDC1's INTSTAT from USBDC0's
# vector and publish the bits into mcu_intr_rcv.usb instead of
# mcu_intr_rcv.usb_dev1, consuming USBDC1's EP0OUT SETUP events and hanging
# the control transfer. USBDC1 is selected at RUNTIME instead, with
# usb_select_device(1) plus the USB_DEV_CSR_BASE_ADDR / USB_DEV_MEM_BASE_ADDR
# retargeting at the top of the .c file.
#
# BUILD_CFLAGS reaches gcc via TEST_CFLAGS; this fragment is included after
# TEST_CFLAGS is defined, but TEST_CFLAGS is a recursive variable, so
# appending here still takes effect.
BUILD_CFLAGS += -DUSB_HUB_COMPOUND_DEV1_IRQ

# ---------------------------------------------------------------------------
# 2. Runtime plusargs
# ---------------------------------------------------------------------------
# All testbench-side enables are RUNTIME plusargs checked with
# $test$plusargs(), not compile-time `ifdefs, so one simv image is reusable
# across every test.

# UVM test to run.
VCS_SIM_OPTS += +UVM_TESTNAME=caliptra_ss_usb_hs_dev1_hub_config_descriptor_test

# Activates the testbench loopback that ORs cptra_ss_usb_dev1_irq_o onto
# cptra_ss_mcu_ext_int[6] in caliptra_ss_top_tb.sv. The loopback is always
# compiled in and is gated only by this plusarg.
VCS_SIM_OPTS += +USB_HUB_COMPOUND_DEV1_IRQ=1
