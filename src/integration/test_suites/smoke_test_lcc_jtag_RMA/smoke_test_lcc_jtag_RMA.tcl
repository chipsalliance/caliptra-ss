# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

init

set script_dir [file dirname [info script]]
source [file join $script_dir common.tcl]

array set TEST_UNLOCKED_TOKEN {
    0 0xef1fadea
    1 0xadfc9693
    2 0x421748a2
    3 0xf12a5911
}
set dlen_words [array size TEST_UNLOCKED_TOKEN]
set dlen_bytes [expr {$dlen_words * 4}]

# Call the transition_state function
lcc_initialization
transition_state 0x1 0xef1fadea 0xadfc9693 0x421748a2 0xf12a5911 0x1

shutdown
