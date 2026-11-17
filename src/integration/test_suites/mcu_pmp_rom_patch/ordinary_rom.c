// SPDX-License-Identifier: Apache-2.0
#include <stdint.h>

volatile uint32_t ordinary_output;

// Adjust and publish a sample, then return its folded value.
uint32_t ordinary_rom_work(uint32_t input) {
    uint32_t value = (input ^ 0x5a5a5a5au) + 17u;
    ordinary_output = value;
    return value + (value >> 8);
}
