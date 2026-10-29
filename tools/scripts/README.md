# SPDX-License-Identifier: Apache-2.0
# 
# # Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# # http://www.apache.org/licenses/LICENSE-2.0 
# # Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# **aha_poc** #

## **Overview** ##

Internal hands-on README describing use of Microsoft Playbook to build Caliptra project.
External integrators: review README.md at Repository root.

## UVM RAL generation

`gen_ral.py` generates interface-local UVM packages or include files, plus a
SystemVerilog base-address configuration package, from schema-version-2 YAML
recipes. For example, from the repository root:

```sh
python3 tools/scripts/gen_ral.py -h
python3 tools/scripts/gen_ral.py --recipe src/usb/rdl/ral_exports.yml
python3 tools/scripts/gen_ral.py --recipe src/usb/rdl/ral_exports.yml --check
```

`-h`/`--help` is a self-contained reference for all recipe fields, types,
defaults, path rules, generated outputs, base-address handling, and exit codes.
It includes complete, runnable RDL and YAML examples.

Each interface directly names the RDL component to configure. For example:

```yaml
schema_version: 2
config_output: generated/example_config_pkg.sv
interfaces:
  - name: packet
    rdl:
      file: packet_memory.rdl
      definition: packet_memory
      parameters:
        ROWS: 512
      include_paths: []
      defines: {}
    base_address: 0x1000
    output:
      path: generated/packet_ral_pkg.sv
      class_name: packet_ral
      memory_instance: storage
```

The `--recipe` path is relative to the invocation directory. All paths inside
the YAML are relative to the recipe directory; absolute paths are accepted,
but YAML paths do not expand `~` or environment variables.
`rdl.file` is one entry file; its includes provide dependencies.
`rdl.definition` must name an address map or memory. `rdl.parameters` is a
required mapping, possibly empty, of scalar unsigned 64-bit integer, boolean, or string
overrides. Values are passed to the RDL compiler, not evaluated as Python or
interpolated as RDL expressions. Optional `rdl.defines` is a mapping of
preprocessor values; `rdl.include_paths` is an ordered list of search directories.

The example requires a local `packet_memory` definition with a `ROWS`
parameter. For a standalone memory, the generator creates and cleans up a
temporary RDL wrapper, forwarding parameters into an external memory at
offset zero before elaboration. The example produces
`packet_ral.storage.m_mem`, preserving memory width, depth, access properties,
and virtual registers. The optional `memory_instance` defaults to `memory`
and is invalid for an address-map input.

`output.class_name` is required. `output.format` defaults to `package`
(`.sv`); `include` requires `.svh`. Package names come from file stems.
`reuse_class_definitions` and `use_uvm_factory` both default to `false`.
Class reuse may change names according to the RDL types; combinations that
cannot honor the requested top `class_name` fail explicitly.

`base_address` is a required unsigned 64-bit byte address. The complete RDL
aperture must fit that range. `config_output` emits
`<UPPERCASE_INTERFACE_NAME>_BASE_ADDRESS` constants, such as
`PACKET_BASE_ADDRESS`, as 64-bit values. Generated RAL children remain
zero-based: the consuming testbench must apply each constant exactly once
at its corresponding root map and check it fits the physical bus. The USB TB
does this in `usb_reg_model.svh`. Equal bases on separate interfaces are legal.
The recipe configures RAL, not DUT parameters or bus translation.

Duplicate YAML keys, interface names/base symbols, package/top-class names or include guards,
invalid identifiers/options, and conflicting output/input paths are errors.
Each interface generates its own model even when RDL inputs are shared.
All outputs are rendered before writing; unchanged outputs are not rewritten.
`--check` reports missing or stale models and configuration without writing
outputs. No register RTL, software headers, documentation, or manifests are
generated.


## **Workspace Setup** ##

### 1. Create a workspace as shown [here](https://dev.azure.com/ms-tsd/Documents/_wiki/wikis/Documents.wiki/114/Workspace-Commands).

Preferred command for making a workspace with this repo,

`make-workspace --project AHA_POC --top <Please_Add_TOP_NAME_Here> --directory integration_lib`


or,


`make-workspace --url git@ssh.dev.azure.com:v3/ms-tsd/AHA_POC/Caliptra --directory integration_lib`

### 2. Add comodules and then, recursively pull all comodules into the workspace (as per the tags specified in .git-comodules).

`pb workspace update`

<br>

# **Build Command:** #

`pb fe build --tb <top_from_compilespecs>::<compile_unit_name>_tb`


or,


`pb fe build --tb integration_lib::integration_tb`


or,


`pb fe build --tb integration_lib::integration_top`


or with IUS,


`pb fe build --tb integration_lib::integration_top --tool ius --targets packages rtl elab --options rtl="+define+TSD_DISABLE_ASSERTIONS"`


<br>

# **Lint Command:** #


`pb fe lint rtl --tb <top_from_compilespecs>::<compile_unit_name>_tb`


or,


`pb fe lint rtl --tb integration_lib::integration_top`


<br>
