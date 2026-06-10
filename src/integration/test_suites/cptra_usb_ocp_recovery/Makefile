# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0

TESTNAME ?= cptra_usb_ocp_recovery
CALIPTRA_ROOT ?= $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl
AUX_HEADER_FILES := $(CALIPTRA_SS_ROOT)/src/integration/test_suites/libs/cptra_usb_ocp_recovery/cptra_usb_ocp_recovery.h $(CALIPTRA_SS_ROOT)/src/integration/rtl/soc_address_map/soc_address_map.h
AUX_OFILES := cptra_usb_ocp_recovery_lib.o
AUX_LIB_DIR := $(CALIPTRA_SS_ROOT)/src/integration/test_suites/libs/cptra_usb_ocp_recovery

.PHONY: all program.hex

all: program.hex

program.hex:
	make -f $(CALIPTRA_ROOT)/tools/scripts/Makefile \
		CALIPTRA_INTERNAL_TRNG=0 \
		TEST_DIR=$(CALIPTRA_SS_ROOT)/src/integration/test_suites/$(TESTNAME) \
		AUX_HEADER_FILES="$(AUX_HEADER_FILES)" \
		AUX_OFILES="$(AUX_OFILES)" \
		AUX_LIB_DIR="$(AUX_LIB_DIR)" \
		TESTNAME=$(TESTNAME) \
		program.hex
