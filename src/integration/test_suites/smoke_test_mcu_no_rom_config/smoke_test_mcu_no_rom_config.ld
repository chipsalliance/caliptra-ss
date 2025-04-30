
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

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  
  . = 0x21c00000;
  .text   : { *(.text*) ; . = ALIGN(4); } =0x0000,
  _text_end = .;
  .rodata : { *(.rodata*) *(.srodata*) ; . = ALIGN(4); } =0x0000,
  _rodata_end = .;

  .dccm : { *(.dccm*) ; . = ALIGN(4); } =0x0000,
  _dccm_end = .;
  .data : { *(.data) *(.data.*) *(.sdata) *(.sdata.*) ; . = ALIGN(4); } =0x0000,
  _data_end = .;
  .bss : { *(.bss) *(.sbss) ; . = ALIGN(4); } =0x0000,
  _bss_end = .;

  STACK = ALIGN(16) + 0x1000;
  ASSERT( STACK < 0x21C7FFFF, "ERROR: STACK allocation exceeds MCU SRAM Size 512KiB")
}