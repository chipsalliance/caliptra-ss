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
# Full-speed per-port hub L1 suite. The HS twin
# (caliptra_ss_usb_dual_device_hs_hub_port_l1) needs no .mk at all because it
# takes the base test's HS defaults and passes everything else through its yml
# plusargs. This file exists only for the full-speed guard below.
#
# The actual line speed is not assumed: +usb_fs_speed_check arms
# caliptra_ss_usb_fs_speed_checker.sv, which verifies XcvrSelect/TermSelect and
# the measured RXValid byte period on the UTMI interface. Without it a run in
# which the firmware's HUB_CTRL.FORCE_FULLSPEED or the test class's
# high_speed_capable=0 silently failed to take effect would still pass - it
# would just be re-testing the HS leg under an FS name.
#
# Note the speed forcing this checks is hub-wide, not per-port: the compound IP
# exposes FORCE_FULLSPEED only through HUB_CTRL bit 21, so both downstream
# devices come up at the same speed and there is no mixed-speed variant of the
# per-port L1 scenario.
VCS_SIM_OPTS += +usb_fs_speed_check=1
