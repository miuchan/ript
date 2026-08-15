#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

if ! audit_output="$(lake env lean Ript/Audit/AxiomChecks.lean 2>&1)"; then
  printf '%s\n' "$audit_output" >&2
  exit 1
fi

audit_targets="$(sed -n 's/^#print axioms //p' Ript/Audit/AxiomChecks.lean)"
documented_targets="$(sed -n 's/^| `\([^`]*\)` |.*/\1/p' AXIOMS.md)"

if [[ -z "$audit_targets" ]]; then
  printf 'Axiom audit has no theorem targets.\n' >&2
  exit 1
fi

while IFS= read -r target; do
  matches="$(printf '%s\n' "$audit_output" | awk -v prefix="'$target' " \
    'index($0, prefix) == 1')"
  match_count="$(printf '%s\n' "$matches" | awk 'NF { count++ } END { print count + 0 }')"

  if [[ "$match_count" -ne 1 ]]; then
    printf 'Expected exactly one axiom report for %s, found %s.\n%s\n' \
      "$target" "$match_count" "$audit_output" >&2
    exit 1
  fi

  if [[ "$matches" != "'$target' does not depend on any axioms" && \
        "$matches" != "'$target' depends on axioms: [propext]" && \
        "$matches" != "'$target' depends on axioms: [Quot.sound]" && \
        "$matches" != "'$target' depends on axioms: [propext, Quot.sound]" ]]; then
    printf 'Axiom allowlist violation for %s:\n%s\n' "$target" "$matches" >&2
    exit 1
  fi

  if ! printf '%s\n' "$documented_targets" | grep -Fqx "$target"; then
    printf 'AXIOMS.md is missing the audited theorem %s.\n' "$target" >&2
    exit 1
  fi
done <<< "$audit_targets"

while IFS= read -r target; do
  if ! printf '%s\n' "$audit_targets" | grep -Fqx "$target"; then
    printf 'AXIOMS.md contains a stale theorem entry: %s.\n' "$target" >&2
    exit 1
  fi
done <<< "$documented_targets"

printf 'Axiom audit matches the documented allowlist.\n'
