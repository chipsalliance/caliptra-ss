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
#ifndef TRACE_BUFFER_CSR_HEADER
#define TRACE_BUFFER_CSR_HEADER


#define TRACE_BUFFER_CSR_BASE_ADDR                                                                  (0x0)
#define TRACE_BUFFER_CSR_STATUS                                                                     (0x0)
#ifndef TRACE_BUFFER_CSR_STATUS
#define TRACE_BUFFER_CSR_STATUS                                                                     (0x0)
#define TRACE_BUFFER_CSR_STATUS_WRAPPED_LOW                                                         (0)
#define TRACE_BUFFER_CSR_STATUS_WRAPPED_MASK                                                        (0x1)
#define TRACE_BUFFER_CSR_STATUS_VALID_DATA_LOW                                                      (1)
#define TRACE_BUFFER_CSR_STATUS_VALID_DATA_MASK                                                     (0x2)
#endif
#define TRACE_BUFFER_CSR_CONFIG                                                                     (0x4)
#ifndef TRACE_BUFFER_CSR_CONFIG
#define TRACE_BUFFER_CSR_CONFIG                                                                     (0x4)
#endif
#define TRACE_BUFFER_CSR_DATA                                                                       (0x8)
#ifndef TRACE_BUFFER_CSR_DATA
#define TRACE_BUFFER_CSR_DATA                                                                       (0x8)
#endif
#define TRACE_BUFFER_CSR_WRITE_PTR                                                                  (0xc)
#ifndef TRACE_BUFFER_CSR_WRITE_PTR
#define TRACE_BUFFER_CSR_WRITE_PTR                                                                  (0xc)
#endif
#define TRACE_BUFFER_CSR_READ_PTR                                                                   (0x10)
#ifndef TRACE_BUFFER_CSR_READ_PTR
#define TRACE_BUFFER_CSR_READ_PTR                                                                   (0x10)
#endif


#endif