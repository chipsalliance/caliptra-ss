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
# Per-test makefile fragment, pulled in by tools/scripts/Makefile through
# "-include $(TEST_DIR)/$(TESTNAME).mk". It is read only when
# TESTNAME=caliptra_ss_usb_fs_clock, so it cannot affect any other test.
#
# Enables caliptra_ss_usb_fs_speed_checker.sv, which is instantiated in
# caliptra_ss_top_tb.sv but stays inert unless this plusarg is present. The
# "=1" form is kept for consistency with the test yml; $test$plusargs matches
# on prefix, so the value itself is ignored.
VCS_SIM_OPTS += +usb_fs_speed_check=1
