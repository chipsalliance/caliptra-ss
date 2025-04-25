//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// 
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************

`ifndef CALIPTRA_SS_INCLUDES_SVH
`define CALIPTRA_SS_INCLUDES_SVH

parameter CPTRA_SS_ROM_SIZE_KB = 256;
parameter CPTRA_SS_ROM_DATA_W = 64;
parameter CPTRA_SS_ROM_DEPTH = (CPTRA_SS_ROM_SIZE_KB*1024) / (CPTRA_SS_ROM_DATA_W/8);
parameter CPTRA_SS_ROM_AXI_ADDR_W = $clog2(CPTRA_SS_ROM_SIZE_KB*1024);
parameter CPTRA_SS_ROM_MEM_ADDR_W = $clog2(CPTRA_SS_ROM_DEPTH);

// Interrupt Assignments
// NOTE Vector 0 is reserved by VeeR
`define VEER_INTR_VEC_MCI                 1
`define VEER_INTR_VEC_I3C                 2
`define VEER_INTR_EXT_LSB                 3
    
`endif // CALIPTRA_SS_INCLUDES_SVH
