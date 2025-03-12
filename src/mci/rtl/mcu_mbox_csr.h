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
#ifndef MCU_MBOX_CSR_HEADER
#define MCU_MBOX_CSR_HEADER


#define MCU_MBOX_CSR_BASE_ADDR                                                                      (0x0)
#define MCU_MBOX_CSR_MBOX_SRAM_BASE_ADDR                                                            (0x0)
#define MCU_MBOX_CSR_MBOX_SRAM_END_ADDR                                                             (0x1fffff)
#define MCU_MBOX_CSR_MBOX_LOCK                                                                      (0x200000)
#ifndef MCU_MBOX_CSR_MBOX_LOCK
#define MCU_MBOX_CSR_MBOX_LOCK                                                                      (0x200000)
#define MCU_MBOX_CSR_MBOX_LOCK_LOCK_LOW                                                             (0)
#define MCU_MBOX_CSR_MBOX_LOCK_LOCK_MASK                                                            (0x1)
#endif
#define MCU_MBOX_CSR_MBOX_USER                                                                      (0x200004)
#ifndef MCU_MBOX_CSR_MBOX_USER
#define MCU_MBOX_CSR_MBOX_USER                                                                      (0x200004)
#endif
#define MCU_MBOX_CSR_MBOX_TARGET_USER                                                               (0x200008)
#ifndef MCU_MBOX_CSR_MBOX_TARGET_USER
#define MCU_MBOX_CSR_MBOX_TARGET_USER                                                               (0x200008)
#endif
#define MCU_MBOX_CSR_MBOX_CMD                                                                       (0x20000c)
#ifndef MCU_MBOX_CSR_MBOX_CMD
#define MCU_MBOX_CSR_MBOX_CMD                                                                       (0x20000c)
#endif
#define MCU_MBOX_CSR_MBOX_DLEN                                                                      (0x200010)
#ifndef MCU_MBOX_CSR_MBOX_DLEN
#define MCU_MBOX_CSR_MBOX_DLEN                                                                      (0x200010)
#endif
#define MCU_MBOX_CSR_MBOX_EXECUTE                                                                   (0x200014)
#ifndef MCU_MBOX_CSR_MBOX_EXECUTE
#define MCU_MBOX_CSR_MBOX_EXECUTE                                                                   (0x200014)
#define MCU_MBOX_CSR_MBOX_EXECUTE_EXECUTE_LOW                                                       (0)
#define MCU_MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK                                                      (0x1)
#endif


#endif