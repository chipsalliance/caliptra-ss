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

// NOTE: This file is used for testing in situations where a program running on
//       the MCU needs to reason about read-lock CSRs. Those CSRs have addresses
//       defined by the SOC address map. In this file, we pair the two together.
//
//       This C file is generated from a template. The template doesn't depend
//       on SOC-level information but the generated C file references names that
//       are defined in soc_address_map.h.
<%!
    from lib.otp_mem_map import LockType
%>\

#include <stdint.h>
#include "fuse_ctrl_mmap.h"
#include "soc_address_map.h"

const uint32_t read_lock_partition_indices[] = {
% for i, p in enumerate(partitions):
%  if p.read_lock == LockType.CSR:
    ${i},
%  endif
% endfor
    UINT32_MAX
};

const uint32_t read_lock_csr_mapping[] = {
% for p in partitions:
%  if p.read_lock == LockType.CSR:
    SOC_OTP_CTRL_${p.name}_READ_LOCK,
%  endif
% endfor
    UINT32_MAX
};
