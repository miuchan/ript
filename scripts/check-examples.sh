#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

bit_output="$(lake env lean Ript/Examples/BitProcesses.lean)"
expected_bit_output=$'true\ntrue\ntrue'

if [[ "$bit_output" != "$expected_bit_output" ]]; then
  printf 'Bit-process example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_bit_output" "$bit_output" >&2
  exit 1
fi

stochastic_output="$(lake env lean Ript/Examples/StochasticBits.lean)"
expected_stochastic_output=$'true\ntrue\ntrue\ntrue\ntrue'

if [[ "$stochastic_output" != "$expected_stochastic_output" ]]; then
  printf 'Finite-stochastic example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_stochastic_output" "$stochastic_output" >&2
  exit 1
fi

kleisli_output="$(lake env lean Ript/Examples/KleisliBits.lean)"
expected_kleisli_output=$'true\ntrue\ntrue\ntrue'

if [[ "$kleisli_output" != "$expected_kleisli_output" ]]; then
  printf 'Finite-distribution Kleisli example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_kleisli_output" "$kleisli_output" >&2
  exit 1
fi

printf 'Executable examples produced the expected results.\n'
