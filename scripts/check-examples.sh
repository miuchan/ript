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

decision_output="$(lake env lean Ript/Examples/SimpleDecision.lean)"
expected_decision_output=$'true\ntrue\ntrue\ntrue\ntrue\ntrue'

if [[ "$decision_output" != "$expected_decision_output" ]]; then
  printf 'Finite-decision example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_decision_output" "$decision_output" >&2
  exit 1
fi

computation_output="$(lake env lean Ript/Examples/SimpleComputation.lean)"
expected_computation_output=$'true\ntrue\ntrue\ntrue\ntrue\ntrue\ntrue'

if [[ "$computation_output" != "$expected_computation_output" ]]; then
  printf 'Computation example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_computation_output" "$computation_output" >&2
  exit 1
fi

causal_output="$(lake env lean Ript/Examples/SimpleCausalModel.lean)"
expected_causal_output=$'true\ntrue\ntrue\ntrue\ntrue'

if [[ "$causal_output" != "$expected_causal_output" ]]; then
  printf 'Finite-causal example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_causal_output" "$causal_output" >&2
  exit 1
fi

thermal_output="$(lake env lean Ript/Examples/SimpleThermalModel.lean)"
expected_thermal_output=$'true\ntrue\ntrue\ntrue\ntrue\ntrue'

if [[ "$thermal_output" != "$expected_thermal_output" ]]; then
  printf 'Finite-thermal example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_thermal_output" "$thermal_output" >&2
  exit 1
fi

qubit_output="$(lake env lean Ript/Examples/QubitChannel.lean)"
expected_qubit_output=$'true\ntrue'

if [[ "$qubit_output" != "$expected_qubit_output" ]]; then
  printf 'Qubit-channel example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_qubit_output" "$qubit_output" >&2
  exit 1
fi

univalent_output="$(lake env lean Ript/Examples/UnivalentProcessUniverse.lean)"
expected_univalent_output='true'

if [[ "$univalent_output" != "$expected_univalent_output" ]]; then
  printf 'Internally univalent process example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_univalent_output" "$univalent_output" >&2
  exit 1
fi

univalent_completion_output="$(lake env lean Ript/Examples/UnivalentCompletion.lean)"
expected_univalent_completion_output='6'

if [[ "$univalent_completion_output" != "$expected_univalent_completion_output" ]]; then
  printf 'Truncated univalent-completion example output changed.\nExpected:\n%s\nActual:\n%s\n' \
    "$expected_univalent_completion_output" "$univalent_completion_output" >&2
  exit 1
fi

printf 'Executable examples produced the expected results.\n'
