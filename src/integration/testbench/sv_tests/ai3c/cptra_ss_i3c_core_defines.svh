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

//
// Recovery Command Summary
//
// Command (decimal, hex)  Req  Scope  Notes
// ------------------------------------------
// PROT_CAP (34, 0x22)     Y    A      Device Capabilities Information
// DEVICE_ID (35, 0x23)    Y    A      Device identity information
// DEVICE_STATUS (36, 0x24)Y    A      Device status information
// DEVICE_RESET (37, 0x25) N    A      Device reset and control
// RECOVERY_CTRL (38, 0x26)Y    A      Recovery control and image activation
// RECOVERY_STATUS (39, 0x27)N   A      Recovery status information
// HW_STATUS (40, 0x28)    N    R      Hardware status including temperature
// INDIRECT_CTRL (41, 0x29)N    R      Indirect memory window control
// INDIRECT_STATUS (42, 0x2A)N  R      Indirect memory window status
// INDIRECT_DATA (43, 0x2B)N    R      Indirect memory window for pushing recovery image
// VENDOR (44, 0x2C)       N    R      Vendor-defined behavior
// INDIRECT_FIFO_CTRL (45, 0x2D)N R    Indirect FIFO control
// INDIRECT_FIFO_STATUS (46, 0x2E)N R  Indirect FIFO status
// INDIRECT_FIFO_DATA (47, 0x2F)N  R   Indirect FIFO write aperture
//

`define I3C_CORE_PROT_CAP                (7'd34)
`define I3C_CORE_DEVICE_ID               (7'd35)
`define I3C_CORE_DEVICE_STATUS           (7'd36)
`define I3C_CORE_DEVICE_RESET            (7'd37)
`define I3C_CORE_RECOVERY_CTRL           (7'd38)
`define I3C_CORE_RECOVERY_STATUS         (7'd39)
`define I3C_CORE_HW_STATUS               (7'd40)
`define I3C_CORE_INDIRECT_CTRL           (7'd41)
`define I3C_CORE_INDIRECT_STATUS         (7'd42)
`define I3C_CORE_INDIRECT_DATA           (7'd43)
`define I3C_CORE_VENDOR                  (7'd44)
`define I3C_CORE_INDIRECT_FIFO_CTRL      (7'd45)
`define I3C_CORE_INDIRECT_FIFO_STATUS    (7'd46)
`define I3C_CORE_INDIRECT_FIFO_DATA      (7'd47)