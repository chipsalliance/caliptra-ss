//********************************************************************************
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
//********************************************************************************
//
// Minimal NWP C test — mirrors MCU mcu_hello_world.c structure.
// Output goes to NWP UART at 0x10001000 (testbench captures to nwp_console.log).

#include "printf.h"
#include <stdint.h>

volatile char* stdout = (char *)0x10001000;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t main (void) {
    VPRINTF(LOW, "=================\n");
    VPRINTF(LOW, "Hello World from NWP (C test)\n");
    VPRINTF(LOW, "=================\n");
    return 0;
}
