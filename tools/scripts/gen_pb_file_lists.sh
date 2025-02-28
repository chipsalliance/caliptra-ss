#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# 
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
function gen_pb_file_list {
    local cpt_ss_vf_file;
    local cpt_ss_dir;
    local cpt_ss_lib;

    cpt_ss_dir=$1;
    cpt_ss_lib=$2;
    cpt_ss_vf_file=${cpt_ss_dir}/${cpt_ss_lib}.vf

    # Skip UVM file lists, which reference installed libraries external to Caliptra repo
    # UPDATE: UVM file lists are now generated, but skip coverage files since these file
    # lists aren't useful to external integrators
    if [[ $cpt_ss_lib = *"coverage" ]]; then return; fi
    echo "Generating File List for lib [${cpt_ss_lib}] in [${cpt_ss_vf_file}]";
    pb fe file_list --tb caliptra_ss_lib::${cpt_ss_lib} +def-target 'tb' --flat --dir-fmt=+incdir+{directory} --file ${cpt_ss_vf_file};
    # Replace leading portion of Caliptra source paths with ${CALIPTRA_SS_ROOT}
    sed 's,/home.*caliptra-ss/src,\${CALIPTRA_SS_ROOT}/src,' -i ${cpt_ss_vf_file}
    sed 's,/home.*caliptra-ss/third_party,\${CALIPTRA_SS_ROOT}/third_party,' -i ${cpt_ss_vf_file}

    # Replace leading portion of UVM/installed library paths with appropriate ENV VAR
    sed 's,/cad.*avery/,\${AVERY_HOME}/,' -i ${cpt_ss_vf_file}

    # Remove duplicate entries and empty lines from the file
    perl -i -ne 'print if ! $a{$_}++ and /\S/' ${cpt_ss_vf_file}
}

if [[ $(command -v pb) = "" ]]; then
    echo "Enter Caliptra workspace (to make Playbook available) and try again"
    exit 1
fi
if [[ -z ${CALIPTRA_SS_ROOT:+"empty"} ]]; then
    echo "Must run script from within Caliptra Playbook context"
    exit 1
fi
# Get all of the compile.yml from caliptra COMODULE, ignoring the submodule flavors
cal_ymls=$(grep '^\s*\- src' ${CALIPTRA_SS_ROOT}/config/compilespecs.yml | sed 's/^\s*- \(src.*\)/\1/')
declare -A procs;
for i in ${cal_ymls}; do
    cal_ss_dir=$(realpath ${CALIPTRA_SS_ROOT}/$(sed 's,\(src/.\+/config\)/.*,\1,' <<< ${i}))
    cal_ss_libs=$(grep '^\s*provides' ${cal_ss_dir}/compile.yml | sed 's/.*\[\([-_A-Za-z0-9]\+\)\].*/\1/')
    for j in ${cal_ss_libs}; do
        gen_pb_file_list ${cal_ss_dir} ${j} &
        procs["$i_$j"]=$!
    done
done
echo "waiting for ${procs[@]}"
wait ${procs[@]}
