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

package caliptra_ss_top_pkg;

  localparam int unsigned I3cNumPrivIds = 4;

  // Maximum clock periods in nanoseconds (1 us = 1000 ns).
  localparam realtime CPTRA_SS_CLK_MAX_PERIOD_NS = 1000.0 / 60.0;
  localparam realtime CPTRA_SS_I3C_CLK_MAX_PERIOD_NS = 1000.0 / 333.0;

  parameter lc_ctrl_state_pkg::lc_token_t RndCnstRawUnlockTokenHashed = {
    128'h896e4a11_d1c8cbba_de8a30e6_f0930a4d
  };

endpackage
