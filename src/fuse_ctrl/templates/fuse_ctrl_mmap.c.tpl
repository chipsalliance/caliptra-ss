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
<%!
    from lib.otp_mem_map import Variant

    def lc_state_decode(state):
        return ["LcStRaw",
                "LcStTestUnlocked0", "LcStTestLocked0", "LcStTestUnlocked1", "LcStTestLocked1",
                "LcStTestUnlocked2", "LcStTestLocked2", "LcStTestUnlocked3", "LcStTestLocked3",
                "LcStTestUnlocked4", "LcStTestLocked4", "LcStTestUnlocked5", "LcStTestLocked5",
                "LcStTestUnlocked6", "LcStTestLocked6", "LcStTestUnlocked7",
                "LcStDev", "LcStProd", "LcStProdEnd", "LcStRma", "LcStScrap"
                ].index(state)
%>\

#include "fuse_ctrl_mmap.h"

const partition_t partitions[NUM_PARTITIONS] = {
% for i, p in enumerate(partitions):
    // ${p.name}
    {
        .index = ${i},
        .address = ${"0x%04X" % p.offset},
<%
  # If there is a digest for the partition, it comes after all the explicit
  # items defined for the partition. This is the last item (at index -1) unless
  # there is also a zeroization status, which would come afterwards. In that
  # situation it's the second-last item (at index -2).
  digest_addr = 0
  zer_addr = 0
  if p.sw_digest or p.hw_digest:
    digest_item = p.items[-2] if p.zeroizable else p.items[-1]
    digest_addr = digest_item.offset
  if p.zeroizable:
    zer_addr = p.items[-1].offset

  if p.variant == Variant.Buffered:
    var_idx = 0
  elif p.variant == Variant.Unbuffered:
    var_idx = 1
  else:
    assert(p.variant == Variant.LifeCycle)
    var_idx = 2
%>\
        .digest_address = ${"0x%04X" % digest_addr},
        .zer_address = ${"0x%04X" % zer_addr},
        .variant = ${var_idx},
        .granularity = ${64 if p.secret else 32},
        .is_secret = ${"true" if p.secret else "false"},
        .hw_digest = ${"true" if p.hw_digest else "false"},
        .sw_digest = ${"true" if p.sw_digest else "false"},
        .has_ecc = ${"true" if p.integrity else "false"},
        .lc_phase = ${lc_state_decode(p.lc_phase)},
        .is_lifecycle = ${"true" if p.variant == Variant.LifeCycle else "false"},
        .num_fuses = ${len(p.items)},
        .fuses = ${p.name.lower() + "_fuses"}
    },
% endfor
};

% for i, p in enumerate(partitions[:len(partitions)]):
const uint32_t ${p.name.lower()}_fuses[] = {
<%
  num_extra_items = (p.hw_digest or p.sw_digest) + p.zeroizable
  listed_items = p.items[:-num_extra_items] if num_extra_items else p.items
%>\
  % for j, f in enumerate(listed_items):
<% comma = "," if j < len(listed_items) - 1 else "" %>\
    ${f.name}${comma}
  % endfor
};
% endfor
