#********************************************************************************
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
#********************************************************************************

OUTPUT_ARCH("riscv")
ENTRY(_start)
SECTIONS {
  
  . = 0x50000000;
  .dccm : { *(.dccm) }
  __dccm_end = .;
  
  .data : { *(.data) *(.data.*) *(.rodata) *(.rodata.*) *(.srodata) *(.srodata.*) }
  __data_end = .;
  
  .bss : { *(.bss) *(.sbss) *(.bss.*) *(.sbss.*) }
  __bss_end = .;
  
  STACK = ALIGN(16) + 0x1000;
  ASSERT((STACK < 0x50004000), "ERROR: Stack overflows the DCCM")
  
  . = 0x80000000;
  .text : { *(.text) *(.text.*) }
  __text_end = .;

  
  ASSERT((__text_end < 0x80010000), "ERROR: Program overflows ROM")
  
  . = 0x21000414;
  .data.io : { *(.data.io) }
}
