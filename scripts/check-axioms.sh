#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

if ! audit_output="$(lake env lean Ript/Audit/AxiomChecks.lean 2>&1)"; then
  printf '%s\n' "$audit_output" >&2
  exit 1
fi

# Do not feed `grep -q` through a pipeline under `pipefail`: once `grep`
# finds a match, the producer can receive SIGPIPE and invert the result.
if grep -Fq 'error:' <<< "$audit_output"; then
  printf '%s\n' "$audit_output" >&2
  exit 1
fi

normalized_audit_output="$(printf '%s\n' "$audit_output" | awk '
  pending != "" {
    sub(/^[[:space:]]+/, "")
    pending = pending " " $0
    if ($0 ~ /]$/) {
      print pending
      pending = ""
    }
    next
  }
  /depends on axioms: \[/ && $0 !~ /]$/ {
    pending = $0
    next
  }
  { print }
  END {
    if (pending != "") {
      print pending
    }
  }
')"

audit_targets="$(sed -n 's/^#print axioms //p' Ript/Audit/AxiomChecks.lean)"
documented_targets="$(sed -n 's/^| `\([^`]*\)` |.*/\1/p' AXIOMS.md)"
documented_axioms="$(sed -n 's/^| `\([^`]*\)` | `\([^`]*\)` |.*/\1|\2/p' AXIOMS.md)"

if [[ -z "$audit_targets" ]]; then
  printf 'Axiom audit has no theorem targets.\n' >&2
  exit 1
fi

while IFS= read -r target; do
  matches="$(printf '%s\n' "$normalized_audit_output" | awk -v prefix="'$target' " \
    'index($0, prefix) == 1')"
  match_count="$(printf '%s\n' "$matches" | awk 'NF { count++ } END { print count + 0 }')"

  if [[ "$match_count" -ne 1 ]]; then
    printf 'Expected exactly one axiom report for %s, found %s.\n%s\n' \
      "$target" "$match_count" "$normalized_audit_output" >&2
    exit 1
  fi

  if [[ "$matches" != "'$target' does not depend on any axioms" && \
        "$matches" != "'$target' depends on axioms: [propext]" && \
        "$matches" != "'$target' depends on axioms: [Quot.sound]" && \
        "$matches" != "'$target' depends on axioms: [propext, Quot.sound]" && \
        "$matches" != "'$target' depends on axioms: [propext, Classical.choice, Quot.sound]" ]]; then
    printf 'Axiom allowlist violation for %s:\n%s\n' "$target" "$matches" >&2
    exit 1
  fi

  documented="$(printf '%s\n' "$documented_axioms" | awk -F'|' -v target="$target" \
    '$1 == target { print $2 }')"

  if [[ -z "$documented" ]]; then
    printf 'AXIOMS.md is missing the audited theorem %s.\n' "$target" >&2
    exit 1
  fi

  if [[ "$matches" == "'$target' does not depend on any axioms" ]]; then
    actual='none'
  else
    actual="${matches#\'$target\' depends on axioms: }"
  fi

  if [[ "$actual" != "$documented" ]]; then
    printf 'Documented axioms differ for %s.\nExpected: %s\nActual: %s\n' \
      "$target" "$documented" "$actual" >&2
    exit 1
  fi

  if ! grep -Fqx "$target" <<< "$documented_targets"; then
    printf 'AXIOMS.md is missing the audited theorem %s.\n' "$target" >&2
    exit 1
  fi
done <<< "$audit_targets"

while IFS= read -r target; do
  if ! grep -Fqx "$target" <<< "$audit_targets"; then
    printf 'AXIOMS.md contains a stale theorem entry: %s.\n' "$target" >&2
    exit 1
  fi
done <<< "$documented_targets"

printf 'Axiom audit matches the documented allowlist.\n'
