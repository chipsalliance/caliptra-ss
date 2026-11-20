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

#ifndef FLOW004_H
#define FLOW004_H

#include <stdint.h>

// Test-ROM artifact ABI, not a production firmware/manifest format.
#define FLOW004_MAGIC 0x344F4C46u
#define FLOW004_MANIFEST_MAGIC 0x34464E4Du
#define FLOW004_MCU_PASS 0x34534150u
#define FLOW004_MAX_WORDS 1024u
#define FLOW004_HEADER_BYTES 16u
#define FLOW004_POLL_LIMIT 200000u

typedef struct {
    uint32_t magic;
    uint32_t stage;
    uint32_t payload_bytes;
    uint32_t checksum;
} flow004_header_t;

typedef struct {
    uint32_t magic;
    uint32_t mcu_destination;
    uint32_t mcu_payload_bytes;
    uint32_t mcu_checksum;
} flow004_manifest_t;

typedef struct {
    uint32_t abi;
    void (*receive_stage)(uint32_t stage);
    void (*complete)(void);
} flow004_services_t;

static inline uint32_t flow004_checksum(const uint8_t *bytes, uint32_t count)
{
    uint32_t hash = 2166136261u;
    for (uint32_t i = 0u; i < count; ++i) {
        hash = (hash ^ bytes[i]) * 16777619u;
    }
    return hash;
}

#endif
