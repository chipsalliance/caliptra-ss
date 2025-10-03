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

#ifndef FUSE_CTRL_MMAP_HEADERS
#define FUSE_CTRL_MMAP_HEADERS

#include <stdbool.h>
#include <stdint.h>

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
    uint32_t        index;
    uint32_t        address;
    uint32_t        digest_address;
    uint32_t        zer_address;
    uint32_t        variant;
    uint32_t        granularity;
    bool            is_secret;
    bool            hw_digest;
    bool            sw_digest;
    bool            has_ecc;
    uint32_t        lc_phase;
    bool            is_lifecycle;
    uint32_t        num_fuses;
    const uint32_t *fuses;
} partition_t;

#define NUM_PARTITIONS ${len(partitions)}

// A map of the NUM_PARTITIONS fuse partitions.
extern const partition_t partitions[];

// Arrays with indices of fuses for each partition.
% for i, p in enumerate(partitions[:len(partitions)]):
extern const uint32_t ${p["name"].lower()}_fuses[];
% endfor

#endif // FUSE_CTRL_MMAP_HEADERS
