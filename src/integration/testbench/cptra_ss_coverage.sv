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

module cptra_ss_coverage(
    input logic clk,
    input logic rst_l
);

    // I3C sideband signals
    logic i3c_payload_available;
    logic i3c_image_activated;

    // Define the coverage group for I3C sideband signals
    covergroup i3c_sideband_cg;
        option.per_instance = 1;
        // Define the coverage points
        coverpoint i3c_payload_available {
            bins available = {1'b1}; // Bin for when payload is available
        }
        coverpoint i3c_image_activated {
            bins activated = {1'b1}; // Bin for when image is activated
        }
    endgroup

    // Instantiate the covergroup
    i3c_sideband_cg i3c_sideband_coverage = new();

    // Task to sample the I3C sideband signals
    task sample_i3c_sideband(
        logic payload_available,
        logic image_activated
    );
        i3c_payload_available = payload_available;
        i3c_image_activated = image_activated;
        // Trigger the covergroup sampling
        i3c_sideband_coverage.sample();
    endtask

endmodule