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
<%
def tab(name):
	return " " * (60-len(r.name))
%>\
#ifndef FUSE_CTRL_ADDRMAP_HEADER
#define FUSE_CTRL_ADDRMAP_HEADER

#define FUSE_CTRL_BASE_ADDR (0x70000000)

% for i, r in enumerate(rb.flat_regs):
#define FUSE_CTRL_${r.name.upper()}${tab(r.name)}(FUSE_CTRL_BASE_ADDR + ${"0x%03X" % (4*i)})
% endfor

% for r in rb.flat_regs:
#define FUSE_CTRL_${r.name.upper()}_WIDTH (${r.get_width()})
<%
offset = 0
%>\
% for f in r.fields:
% if len(r.fields) > 1:
#define FUSE_CTRL_${r.name.upper()}_${f.name.upper()}_WIDTH (${f.bits.width()})
#define FUSE_CTRL_${r.name.upper()}_${f.name.upper()}_OFFSET (${offset})
#define FUSE_CTRL_${r.name.upper()}_${f.name.upper()}_MASK (${f.bits.bitmask()})
% endif
<%
offset += f.bits.width()
%>\
% endfor

% endfor

#endif
