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

#include "flow004.h"

__attribute__((section(".text.entry")))
void image_entry(const flow004_services_t *services)
{
    if (services->abi != FLOW004_MAGIC) {
        return;
    }
    // Only the USB-downloaded ICCM image requests the subsequent stages.
    services->receive_stage(1u);
    services->receive_stage(2u);
    services->complete();
}
