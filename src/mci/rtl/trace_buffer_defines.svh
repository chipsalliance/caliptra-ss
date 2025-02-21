// SPDX-License-Identifier: Apache-2.0
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
//
`ifndef TRACE_BUFFER_DEFINES_HEADER
`define TRACE_BUFFER_DEFINES_HEADER


`define TRACE_BUFFER_CSR_BASE_ADDR                                                                  (32'h0)
`define TRACE_BUFFER_CSR_STATUS                                                                     (32'h0)
`define TRACE_BUFFER_CSR_CONFIG                                                                     (32'h4)
`define TRACE_BUFFER_CSR_DATA                                                                       (32'h8)
`define TRACE_BUFFER_CSR_WRITE_PTR                                                                  (32'hc)
`define TRACE_BUFFER_CSR_READ_PTR                                                                   (32'h10)


`endif