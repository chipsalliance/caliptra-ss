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

parameter CPTRA_SS_MCU_LSU_ARID_WIDTH = 8;
parameter CPTRA_SS_MCU_LSU_AWID_WIDTH = 8;
parameter CPTRA_SS_MCU_IFU_ARID_WIDTH = 8;
parameter CPTRA_SS_MCU_IFU_AWID_WIDTH = 8;

parameter CPTRA_SS_STRAP_CLPTRA_CORE_AXI_USER   = 32'h3; // FIXME make these values modifiable at run-time for testing
parameter CPTRA_SS_STRAP_MCU_LSU_AXI_USER       = 32'h1; // FIXME make these values modifiable at run-time for testing
parameter CPTRA_SS_STRAP_MCU_IFU_AXI_USER       = 32'h2; // FIXME make these values modifiable at run-time for testing

`endif // CPTRA_SS_INCLUDES_SVH
