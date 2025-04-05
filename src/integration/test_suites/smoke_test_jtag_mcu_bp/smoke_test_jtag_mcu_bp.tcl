# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

init

set script_dir [file dirname [info script]]
source [file join $script_dir .. libs jtag common.tcl]

# Success
puts "Writing BOOTFSM GO to end the test"
riscv dmi_write  $MCI_DMI_MCI_BOOTFSM_GO 0x1
set actual [riscv dmi_read $MCI_DMI_MCI_BOOTFSM_GO]
if {[compare $actual 1] != 0} {
    puts "mismatch in register MCI_DMI_MCI_BOOTFSM_GO!"
    shutdown error
}

shutdown