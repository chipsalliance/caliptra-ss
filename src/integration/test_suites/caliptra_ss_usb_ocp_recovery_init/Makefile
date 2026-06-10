# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0

TESTNAME ?= caliptra_ss_usb_ocp_recovery_init
CALIPTRA_TESTNAME ?= cptra_usb_ocp_recovery

.PHONY: all mcu_program.hex cptra_program.hex

all: mcu_program.hex cptra_program.hex

mcu_program.hex cptra_program.hex:
	make -f $(CALIPTRA_SS_ROOT)/tools/scripts/Makefile \
		TESTNAME=$(TESTNAME) \
		CALIPTRA_TESTNAME=$(CALIPTRA_TESTNAME) \
		CALIPTRA_AUX=soc_ifc_ss \
		CALIPTRA_SS_CLK_FREQ=400 \
		mcu_program.hex cptra_program.hex
