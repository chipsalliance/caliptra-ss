# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
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
GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = $(CURDIR)
today=$(shell date +%Y%m%d)

# Define test name
TESTNAME ?= cptra_fw_test_rom
TESTNAME_fw = $(TESTNAME)_fw
TEST_DIR = $(CALIPTRA_SS_ROOT)/src/integration/test_suites/$(TESTNAME)

VPATH = $(TEST_DIR) $(BUILD_DIR)

# Offset calculations for fetching keys from ROM image
KEY_MANIFEST_ECC_PK_COUNT      = 1
KEY_MANIFEST_ECC_PK_SIZE       = 196
KEY_MANIFEST_ECC_PK_ROM_OFFSET = 12
KEY_MANIFEST_ECC_PK_LENGTH     = $(shell bc <<< "$(KEY_MANIFEST_ECC_PK_COUNT)*$(KEY_MANIFEST_ECC_PK_SIZE)")

KEY_MANIFEST_PQC_PK_COUNT      = 1
KEY_MANIFEST_PQC_PK_SIZE       = 1540
KEY_MANIFEST_PQC_PK_ROM_OFFSET = $(shell bc <<< "$(KEY_MANIFEST_ECC_PK_ROM_OFFSET) + $(KEY_MANIFEST_ECC_PK_COUNT)*$(KEY_MANIFEST_ECC_PK_SIZE)")
KEY_MANIFEST_PQC_PK_LENGTH     = $(shell bc <<< "$(KEY_MANIFEST_PQC_PK_COUNT)*$(KEY_MANIFEST_PQC_PK_SIZE)")

KEY_MANIFEST_PK_LENGTH         = $(shell bc <<< "$(KEY_MANIFEST_PQC_PK_LENGTH) + $(KEY_MANIFEST_ECC_PK_LENGTH)")

OWNER_ECC_PK_SIZE              = 96
OWNER_ECC_PK_ROM_OFFSET        = 9168
OWNER_PQC_PK_SIZE              = 2592
OWNER_PQC_PK_ROM_OFFSET        = $(shell bc <<< "$(OWNER_ECC_PK_ROM_OFFSET) + $(OWNER_ECC_PK_SIZE)")

OWNER_PK_LENGTH                = $(shell bc <<< "$(OWNER_PQC_PK_SIZE) + $(OWNER_ECC_PK_SIZE)")

# Targets
all: program.hex

clean:
	rm -rf *.log *.s *.hex *.dis *.size *.tbl .map *.map snapshots \
	*.exe obj* *.o csrc *.csv work \
	dataset.asdb  library.cfg vsimsa.cfg \
	*.h

############ TEST build ###############################

# Build program.hex from RUST executable
program.hex: vendor_pk_hash_val.hex owner_pk_hash_val.hex fw_update.hex $(BUILD_DIR)/$(TESTNAME).extracted $(TEST_DIR)/$(TESTNAME).bin $(TEST_DIR)/$(TESTNAME_fw)
	@-echo "Building program.hex from $(TESTNAME) using Crypto Test rules for pre-compiled RUST executables"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0xC000 --gap-fill 0xFF --no-change-warnings $(BUILD_DIR)/$(TESTNAME) program.hex
	du -b $(BUILD_DIR)/$(TESTNAME) | cut -f1 > $(BUILD_DIR)/$(TESTNAME).size

fw_update.hex: $(BUILD_DIR)/$(TESTNAME).extracted
	@-echo "Building fw_update.hex from $(TESTNAME_fw) using binary objcopy pre-compiled RUST package"
	$(GCC_PREFIX)-objcopy -I binary -O verilog --pad-to 0x20000 --gap-fill 0xFF --no-change-warnings $(BUILD_DIR)/$(TESTNAME_fw) fw_update.hex
	du -b $(BUILD_DIR)/$(TESTNAME_fw) | cut -f1 > $(BUILD_DIR)/fw_update.size

# Extract public keys from ROM binary and dump as hex values
vendor_pk_hash_val.hex: vendor_pk_val.bin
	sha384sum vendor_pk_val.bin | sed 's,\s\+\S\+$$,,' > $(BUILD_DIR)/vendor_pk_hash_val.hex

vendor_pk_val.bin: $(BUILD_DIR)/$(TESTNAME).extracted
	dd ibs=1 obs=1 if=$(BUILD_DIR)/$(TESTNAME_fw) of=vendor_pk_val.bin skip=$(KEY_MANIFEST_ECC_PK_ROM_OFFSET) count=$(KEY_MANIFEST_PK_LENGTH)

owner_pk_hash_val.hex: owner_pk_val.bin
	sha384sum owner_pk_val.bin | sed 's,\s\+\S\+$$,,' > owner_pk_hash_val.hex

owner_pk_val.bin: $(BUILD_DIR)/$(TESTNAME).extracted
	dd ibs=1 obs=1 if=$(BUILD_DIR)/$(TESTNAME_fw) of=owner_pk_val.bin skip=$(OWNER_ECC_PK_ROM_OFFSET) count=$(OWNER_PK_LENGTH)

$(BUILD_DIR)/$(TESTNAME).extracted: $(TEST_DIR)/$(TESTNAME).bin $(TEST_DIR)/$(TESTNAME_fw) copy_caliptra_hex_files
	 cp $(TEST_DIR)/$(TESTNAME).bin $(BUILD_DIR)/$(TESTNAME)
	 cp $(TEST_DIR)/$(TESTNAME_fw) $(BUILD_DIR)/$(TESTNAME_fw)
	 touch $(BUILD_DIR)/$(TESTNAME).extracted

#-- following two files copied to build directory to support csr_write_mpmc_halt() at the end of the test
copy_caliptra_hex_files:
	 cp $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/integration/test_suites/includes/caliptra_defines.h $(BUILD_DIR)
	 cp $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/integration/test_suites/includes/defines.h $(BUILD_DIR)
	 cp $(CALIPTRA_SS_ROOT)/third_party/caliptra-rtl/src/integration/rtl/caliptra_reg_ss/caliptra_reg.h $(BUILD_DIR)

help:
	@echo Make sure the environment variable RV_ROOT is set.
	echo Possible targets: help clean all program.hex

.PHONY: help clean

.ONESHELL:
