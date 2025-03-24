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
//

#ifndef CALIPTRA_SS_LIB
#define CALIPTRA_SS_LIB

void reset_rtl(void);
void mcu_mci_boot_go();
void mcu_mci_poll_exec_lock();
void mcu_mci_req_reset();
void mcu_cptra_fuse_init();
void mcu_cptra_user_init();
void mcu_cptra_poll_mb_ready();
void mcu_cptra_mbox_cmd();

#endif // CALIPTRA_SS_LIB
