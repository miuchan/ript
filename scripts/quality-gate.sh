#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

printf '\n== Source quality ==\n'
./scripts/check-source-quality.sh

printf '\n== Root-module coverage ==\n'
lake exe mk_all --check

printf '\n== Kernel build ==\n'
lake build

printf '\n== Declaration lint ==\n'
lake env lean Ript/Audit/Lint.lean

printf '\n== Executable examples ==\n'
./scripts/check-examples.sh

printf '\n== Axiom allowlist ==\n'
./scripts/check-axioms.sh

printf '\nAll Ript quality gates passed.\n'
