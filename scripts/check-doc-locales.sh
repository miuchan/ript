#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

locales=(en zh-CN ja eo)
documents=(
  README.md
  GETTING_STARTED.md
  ARCHITECTURE.md
  PROJECT_SCOPE.md
  RESEARCH_STATUS.md
  CONTRIBUTING.md
  GOVERNANCE.md
  SECURITY.md
  reference/MODEL_MATRIX.md
  reference/BLUEPRINT.md
  reference/AXIOMS.md
  reference/CONJECTURES.md
)
language_labels=(English 简体中文 日本語 Esperanto)

failed=0
canonical_tail="$(mktemp)"
english_tail="$(mktemp)"
trap 'rm -f "$canonical_tail" "$english_tail"' EXIT

for root_document in README.md CONTRIBUTING.md GOVERNANCE.md SECURITY.md \
  RESEARCH_GOAL.md BLUEPRINT.md MODEL_MATRIX.md AXIOMS.md CONJECTURES.md; do
  if [[ ! -f "$root_document" ]]; then
    printf 'Missing canonical project document: %s\n' "$root_document" >&2
    failed=1
  fi
done

for document in "${documents[@]}"; do
  for locale in "${locales[@]}"; do
    path="docs/$locale/$document"
    if [[ ! -f "$path" ]]; then
      printf 'Missing localized document: %s\n' "$path" >&2
      failed=1
      continue
    fi

    for label in "${language_labels[@]}"; do
      if ! grep -Fq "[$label]" "$path"; then
        printf 'Missing language switch %s in %s\n' "$label" "$path" >&2
        failed=1
      fi
    done
  done
done

legacy_paths=(
  docs/README.zh-CN.md
  docs/README.ja.md
  docs/README.eo.md
  docs/GETTING_STARTED.md
  docs/ARCHITECTURE.md
  docs/PROJECT_SCOPE.md
  docs/RESEARCH_STATUS.md
  docs/GOVERNANCE.md
  docs/SECURITY.md
)

for legacy_path in "${legacy_paths[@]}"; do
  if [[ -e "$legacy_path" ]]; then
    printf 'Legacy documentation path remains after locale migration: %s\n' \
      "$legacy_path" >&2
    failed=1
  fi
done

check_english_reference_mirror() {
  local canonical="$1"
  local mirror="$2"
  local marker="$3"

  awk -v marker="$marker" 'found || index($0, marker) == 1 { found = 1; print }' \
    "$canonical" > "$canonical_tail"
  awk -v marker="$marker" 'found || index($0, marker) == 1 { found = 1; print }' \
    "$mirror" > "$english_tail"

  if [[ ! -s "$canonical_tail" || ! -s "$english_tail" ]] ||
      ! cmp -s "$canonical_tail" "$english_tail"; then
    printf 'English reference mirror is stale: %s\n' "$mirror" >&2
    failed=1
  fi
}

check_english_reference_mirror AXIOMS.md docs/en/reference/AXIOMS.md \
  'The core declares'
check_english_reference_mirror BLUEPRINT.md docs/en/reference/BLUEPRINT.md \
  'This document records'
check_english_reference_mirror CONJECTURES.md docs/en/reference/CONJECTURES.md \
  'This register contains'
check_english_reference_mirror MODEL_MATRIX.md docs/en/reference/MODEL_MATRIX.md \
  'Only implemented'

canonical_axiom_rows="$(awk '/^\| `[^`]+` \|/ { count++ } END { print count + 0 }' AXIOMS.md)"
for locale in zh-CN ja eo; do
  localized_axiom_rows="$(awk '/^\| `[^`]+` \|/ { count++ } END { print count + 0 }' \
    "docs/$locale/reference/AXIOMS.md")"
  if [[ "$localized_axiom_rows" -ne "$canonical_axiom_rows" ]]; then
    printf 'Localized axiom row count differs for %s: expected %s, found %s\n' \
      "$locale" "$canonical_axiom_rows" "$localized_axiom_rows" >&2
    failed=1
  fi
done

if ! ./scripts/sync-doc-reference-tables.sh --check; then
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

printf 'All maintained documents have synchronized four-language mirrors.\n'
