#!/usr/bin/env bash

set -euo pipefail

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

reject_matches() {
  local description="$1"
  local pattern="$2"
  shift 2

  local matches
  local grep_exit
  if matches="$(git grep --untracked -n -E "$pattern" -- "$@")"; then
    printf 'Source quality check failed: %s\n%s\n' "$description" "$matches" >&2
    return 1
  else
    grep_exit=$?
    if [[ "$grep_exit" -ne 1 ]]; then
      printf 'Source quality check could not run: %s\n' "$description" >&2
      return "$grep_exit"
    fi
  fi
}

reject_matches \
  'proof placeholders or compiler-trust escapes are forbidden' \
  '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|sorryAx|Lean\.trustCompiler' \
  '*.lean'

reject_matches \
  'project-specific axioms and constants are forbidden' \
  '^[[:space:]]*((private|protected|local)[[:space:]]+)*(axiom|constant)[[:space:]]' \
  '*.lean'

reject_matches \
  'unsafe declarations are outside the kernel-checked project boundary' \
  '^[[:space:]]*((private|protected|local)[[:space:]]+)*unsafe[[:space:]]+(def|instance)[[:space:]]' \
  '*.lean'

reject_matches \
  'import specific Mathlib modules instead of the full Mathlib umbrella' \
  '^[[:space:]]*((public|meta)[[:space:]]+)*import[[:space:]]+Mathlib[[:space:]]*$' \
  '*.lean'

reject_matches \
  'tracked source and documentation must not contain trailing whitespace' \
  '[[:blank:]]+$' \
  '*.lean' '*.md' '*.json' '*.yml' '*.yaml' '*.sh'

reject_matches \
  'public Markdown must avoid the renderer-blocked operatorname macro' \
  '\\operatorname' \
  '*.md'

markdown_table_errors=0
while IFS= read -r markdown_file; do
  if ! awk '
    function pipe_count(line, copy) {
      copy = line
      return gsub(/\|/, "", copy)
    }

    NR > 1 &&
        $0 ~ /^[[:space:]]*\|[[:space:]]*:?-+/ &&
        $0 !~ /[^|:[:space:]-]/ {
      if (previous !~ /^[[:space:]]*\|/ ||
          pipe_count(previous) != pipe_count($0)) {
        printf "Source quality check failed: malformed Markdown table separator at %s:%d\n", FILENAME, NR
        failed = 1
      }
    }

    { previous = $0 }

    END { exit failed }
  ' "$markdown_file"; then
    markdown_table_errors=1
  fi
done < <(git ls-files --cached --others --exclude-standard -- '*.md')

if [[ "$markdown_table_errors" -ne 0 ]]; then
  exit 1
fi

missing_auto_implicit=0
while IFS= read -r lean_file; do
  if ! grep -q -E '^set_option autoImplicit false[[:space:]]*$' "$lean_file"; then
    printf 'Source quality check failed: %s must set autoImplicit false\n' "$lean_file" >&2
    missing_auto_implicit=1
  fi
done < <(git ls-files --cached --others --exclude-standard -- 'Ript/**/*.lean')

if [[ "$missing_auto_implicit" -ne 0 ]]; then
  exit 1
fi

for shell_file in scripts/*.sh; do
  bash -n "$shell_file"
done

printf 'Source quality checks passed.\n'
