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

task end_test_successful_req();

    tb_services_if.end_test_success = 1'b1;

endtask

task wait_lcc_init();
    $display("[%t]: Waiting for LCC init", $time);
    wait(`MCI_PATH.i_boot_seqr.lc_done);
    $display("[%t]: LCC init complete", $time);
endtask