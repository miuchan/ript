#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

actual_output="$(lake env lean Ript/Examples/BitProcesses.lean)"
expected_output=$'true\ntrue\ntrue'

if [[ "$actual_output" != "$expected_output" ]]; then
  printf 'Executable example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_output" "$actual_output" >&2
  exit 1
fi

printf 'Executable examples produced the expected results.\n'
