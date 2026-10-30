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
# Device-driven L1 exit leg. +usb_lpm_dev_wakeup=1 selects the sequence's
# device-initiated step-7 branch, in which the firmware doorbell is the only
# thing that may START the resume; it must be paired with
# BUILD_CFLAGS="-DUSB_LPM_DEVICE_INITIATED_EXIT=1", which the yml recipe
# supplies. See the suite README for why the two cannot live in one image.
#
# +usb_device_wakeup_check enables caliptra_ss_usb_device_wakeup_checker, which
# is mandatory here rather than extra instrumentation: it watches the DUT's own
# UTMI TXValid with linestate=K and publishes usb_dut_wakeup_k_seen, and the
# sequence's host resume takeover is triggered BY that event. Without it the
# event never fires, the host never terminates the resume, and the DUT parks
# forever in BUS_EVENT_SW_WAKEUP_3, which has no timeout arm. It also supplies
# the CHK_DEVICE_WAKEUP_K verdict.
VCS_SIM_OPTS += +usb_suspend_resume_check=1
VCS_SIM_OPTS += +usb_lpm_dev_wakeup=1
VCS_SIM_OPTS += +usb_device_wakeup_check=1
