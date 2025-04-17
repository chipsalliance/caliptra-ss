//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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

parameter CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER   = 32'h3; // FIXME make these values modifiable at run-time for testing
parameter CPTRA_SS_STRAP_MCU_LSU_AXI_USER       = 32'h1; // FIXME make these values modifiable at run-time for testing
parameter CPTRA_SS_STRAP_MCU_IFU_AXI_USER       = 32'h2; // FIXME make these values modifiable at run-time for testing

// Interrupt Assignments
// NOTE Vector 0 is reserved by VeeR
`define VEER_INTR_VEC_MCI                 1
`define VEER_INTR_VEC_I3C                 2
`define VEER_INTR_EXT_LSB                 3
    
`endif // CPTRA_SS_INCLUDES_SVH
