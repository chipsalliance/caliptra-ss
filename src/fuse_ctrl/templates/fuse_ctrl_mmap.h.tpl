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

#ifndef FUSE_CTRL_MMAP_HEADER
#define FUSE_CTRL_MMAP_HEADERS
<%!
    def lc_state_decode(state):
        return ["LcStRaw",
                "LcStTestUnlocked0", "LcStTestLocked0", "LcStTestUnlocked1", "LcStTestLocked1",
                "LcStTestUnlocked2", "LcStTestLocked2", "LcStTestUnlocked3", "LcStTestLocked3",
                "LcStTestUnlocked4", "LcStTestLocked4", "LcStTestUnlocked5", "LcStTestLocked5",
                "LcStTestUnlocked6", "LcStTestLocked6", "LcStTestUnlocked7",
                "LcStDev", "LcStProd", "LcStProdEnd", "LcStRma", "LcStScrap"
                ].index(state)
%>
typedef enum {
% for i, p in enumerate(partitions):
    // ${p["name"]}
  % for j, f in enumerate(p["items"]):
    % if f["isdigest"] == False and f["iszer"] == False:
      % if i == len(partitions)-1 and j == len(p["items"])-1:
    ${f["name"]} = ${"0x%04X" % f["offset"]}
      % else:
    ${f["name"]} = ${"0x%04X" % f["offset"]},
      % endif
    % endif
  % endfor
% endfor
} fuse_k;

typedef enum {
% for i, p in enumerate(partitions):
    ${p["name"]}${"," if i < len(partitions)-1 else ""}
% endfor
} partition_k;

typedef struct {
    uint32_t index;
    uint32_t address;
    uint32_t digest_address;
    uint32_t zer_address;
    uint32_t variant;
    uint32_t granularity;
    bool is_secret;
    bool hw_digest;
    bool sw_digest;
    bool has_read_lock;
    bool has_ecc;
    uint32_t lc_phase;
    bool is_lifecycle;
    uint32_t num_fuses;
    uint32_t *fuses;
} partition_t;

#define NUM_PARTITIONS ${len(partitions)}

% for i, p in enumerate(partitions[:len(partitions)]):
uint32_t ${p["name"].lower()}_fuses[] = {
  % if (p["hw_digest"] or p["sw_digest"]) and not p["zeroizable"]:
    % for j, f in enumerate(p["items"][:len(p["items"])-1]):
      % if j < len(p["items"])-2:
    ${f["name"]},
      % else:
    ${f["name"]}
      % endif
    % endfor
  % elif (p["hw_digest"] or p["sw_digest"]) and p["zeroizable"]:
    % for j, f in enumerate(p["items"][:len(p["items"])-2]):
      % if j < len(p["items"])-3:
    ${f["name"]},
      % else:
    ${f["name"]}
      % endif
    % endfor
  % else:
    % for j, f in enumerate(p["items"][:len(p["items"])]):
      % if j < len(p["items"])-1:
    ${f["name"]},
      % else:
    ${f["name"]}
      % endif
    % endfor
  % endif
};
% endfor

partition_t partitions[NUM_PARTITIONS] = {
% for i, p in enumerate(partitions):
    // ${p["name"]}
    {
        .index = ${i},
        .address = ${"0x%04X" % p["offset"]},
% if p["sw_digest"] or p["hw_digest"]:
  % if p["zeroizable"]:
        .digest_address = ${"0x%04X" % p["items"][len(p["items"])-2]["offset"]},
  % else:
        .digest_address = ${"0x%04X" % p["items"][len(p["items"])-1]["offset"]},
  % endif
% else:
        .digest_address = 0x0000,
% endif
% if p["zeroizable"]:
        .zer_address = ${"0x%04X" % p["items"][len(p["items"])-1]["offset"]},
% else:
        .zer_address = 0x0000,
% endif
        .variant = ${0 if p["variant"] == "Buffered" else (1 if p["variant"] == "Unbuffered" else 2)},
        .granularity = ${64 if p["secret"] else 32},
        .is_secret = ${"true" if p["secret"] else "false"},
        .hw_digest = ${"true" if p["hw_digest"] else "false"},
        .sw_digest = ${"true" if p["sw_digest"] else "false"},
        .has_read_lock = ${"true" if p["read_lock"] == "CSR" else "false"},
        .has_ecc = ${"true" if p["integrity"] else "false"},
        .lc_phase = ${lc_state_decode(p["lc_phase"])},
        .is_lifecycle = ${"true" if p["variant"] == "LifeCycle" else "false"},
        .num_fuses = ${len(p["items"])-1},
        .fuses = ${p["name"].lower() + "_fuses"}
    },
% endfor
};

#endif // FUSE_CTRL_MMAP_HEADER