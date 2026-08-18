#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

check_only=0
if [[ "${1:-}" == "--check" ]]; then
  check_only=1
elif [[ $# -ne 0 ]]; then
  printf 'Usage: %s [--check]\n' "$0" >&2
  exit 2
fi

generated_rows="$(mktemp)"
generated_file="$(mktemp)"
trap 'rm -f "$generated_rows" "$generated_file"' EXIT

awk '/^\| `[^`]+` \|/ { print }' AXIOMS.md > "$generated_rows"

update_axiom_table() {
  local target="$1"
  awk -v rows="$generated_rows" '
    $0 == "<!-- BEGIN GENERATED AXIOM ROWS -->" {
      print
      while ((getline row < rows) > 0) print row
      close(rows)
      generated = 1
      next
    }
    $0 == "<!-- END GENERATED AXIOM ROWS -->" {
      generated = 0
      print
      next
    }
    !generated { print }
  ' "$target" > "$generated_file"

  if [[ "$check_only" -eq 1 ]]; then
    if ! cmp -s "$target" "$generated_file"; then
      printf 'Localized axiom table is stale: %s\n' "$target" >&2
      return 1
    fi
  else
    cp "$generated_file" "$target"
  fi
}

for target in \
  docs/zh-CN/reference/AXIOMS.md \
  docs/ja/reference/AXIOMS.md \
  docs/eo/reference/AXIOMS.md; do
  update_axiom_table "$target"
done

if [[ "$check_only" -eq 1 ]]; then
  printf 'Localized reference tables are synchronized.\n'
else
  printf 'Synchronized localized reference tables.\n'
fi
