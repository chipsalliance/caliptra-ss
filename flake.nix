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
{
  description = "caliptra-ss Nix Packages and Environments";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    flake-utils.url = "github:numtide/flake-utils";

    ##########
    # PYTHON #
    ##########

    pyproject-nix = {
      url = "github:pyproject-nix/pyproject.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    pyproject-build-systems = {
      url = "github:pyproject-nix/build-system-pkgs";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.pyproject-nix.follows = "pyproject-nix";
      inputs.uv2nix.follows = "uv2nix";
    };
    uv2nix = {
      url = "github:pyproject-nix/uv2nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.pyproject-nix.follows = "pyproject-nix";
    };
  };

  outputs = inputs: let
    all_system_outputs = inputs.flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import inputs.nixpkgs {
        inherit system;
      };
      python_dvsim = pkgs.callPackage ./tools/dvsim/python {inherit inputs;};
      python_reg_gen = pkgs.callPackage ./tools/scripts/python {inherit inputs;};

      # Environment variables derivable from the repo layout.
      # Variables that cannot be auto-set here:
      #   CALIPTRA_WORKSPACE — user-specific parent dir for verilator scratch output
      #   RV_ROOT            — external VeeR-EL2 checkout (not a submodule)
      commonShellHook = ''
        export CALIPTRA_ROOT="$(git rev-parse --show-toplevel)"
        export ADAMSBRIDGE_ROOT="$CALIPTRA_ROOT/submodules/adams-bridge"
      '';
      dvsimShellHook = commonShellHook + ''
        # EDA simulators (e.g. Cadence's xrun) invoke a vendor-bundled gcc to compile C DPI
        # sources, and do not reliably pick up openssl from the environment's standard
        # compiler search paths. Export fixed env vars pointing at the openssl headers and
        # libraries provided by this devshell so dvsim hjson can thread them to the
        # simulator's C compiler as explicit -I/-L flags, making the build reproducible
        # across host distros.
        export OPENSSL_INCLUDE_DIR="${pkgs.openssl.dev}/include"
        export OPENSSL_LIB_DIR="${pkgs.openssl.out}/lib"
        # Vendor EDA binaries (e.g. Verdi's libnovas.so loaded by simv) are foreign ELFs
        # that dlopen shared libs via the loader's default search path. mkShell does not
        # populate LD_LIBRARY_PATH for runtime, so expose the libs they DT_NEED here.
        export LD_LIBRARY_PATH="${pkgs.lib.makeLibraryPath [
          pkgs.zlib
          pkgs.numactl
          pkgs.ncurses
          pkgs.stdenv.cc.cc.lib
        ]}''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
      '';
    in {
      devShells = rec {
        default = caliptra-dvsim;
        caliptra-dvsim = pkgs.mkShell {
          name = "caliptra-dvsim";
          packages = ([
            python_dvsim
          ]) ++ (with pkgs; [
            uv
            # Needed by the AES DPI model's crypto.c (openssl/conf.h etc.); xrun also links -lcrypto.
            openssl
            openssl.dev
          ]);
          shellHook = dvsimShellHook;
        };
        caliptra-reg-gen = pkgs.mkShell {
          name = "caliptra-reg-gen";
          packages = [
            python_reg_gen
          ];
          shellHook = commonShellHook;
        };
      };
    });
  in
    all_system_outputs;
}
