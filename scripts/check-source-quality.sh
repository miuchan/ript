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

# Validate complete GFM table blocks, not just their separator rows. A single
# missing separator or data cell makes GitHub render the whole block as raw
# pipe-delimited prose, which is easy to miss in source review.
markdown_table_errors=0
while IFS= read -r markdown_file; do
  if ! awk '
    function pipe_count(line, i, character, in_code, count) {
      for (i = 1; i <= length(line); i += 1) {
        character = substr(line, i, 1)
        if (character == "\\") {
          i += 1
        } else if (character == "`") {
          while (i < length(line) && substr(line, i + 1, 1) == "`") {
            i += 1
          }
          in_code = !in_code
        } else if (character == "|" && !in_code) {
          count += 1
        }
      }
      return count
    }

    function is_table_row(line) {
      return line ~ /^[[:space:]]*\|.*\|[[:space:]]*$/
    }

    function is_separator(line) {
      return line ~ /^[[:space:]]*\|[[:space:]]*:?-/ &&
        line !~ /[^|:[:space:]-]/
    }

    {
      if (in_table) {
        if (is_table_row($0)) {
          if (pipe_count($0) != expected_pipes) {
            printf "Source quality check failed: Markdown table row at %s:%d has %d pipes; expected %d\n", FILENAME, NR, pipe_count($0), expected_pipes
            failed = 1
          }
        } else {
          in_table = 0
        }
      }

      if (NR > 1 && is_separator($0)) {
        if (!is_table_row(previous) ||
            pipe_count(previous) != pipe_count($0)) {
          printf "Source quality check failed: malformed Markdown table separator at %s:%d\n", FILENAME, NR
          failed = 1
        }
        in_table = 1
        expected_pipes = pipe_count($0)
      }

      previous = $0
    }

    END { exit failed }
  ' "$markdown_file"; then
    markdown_table_errors=1
  fi
done < <(git ls-files --cached --others --exclude-standard -- '*.md')

if [[ "$markdown_table_errors" -ne 0 ]]; then
  exit 1
fi

# The canonical capability matrix is deliberately a standard GFM table so it
# renders in GitHub and other Markdown clients. Its schema is public API:
# validate the heading, separator, all 14 rows, and all 10 columns explicitly.
if ! awk '
  function pipe_count(line, copy) {
    copy = line
    return gsub(/\|/, "", copy)
  }

  { source_line[NR] = $0 }

  /^\| Model \| Sequential \| Tensor \| Discard \| Copy \| Convex \| Causal \| Decision \| Thermal \| Computable \|$/ {
    header_line = NR
    expected_pipes = pipe_count($0)
    in_matrix = 1
    next
  }

  in_matrix && NR == header_line + 1 {
    if ($0 !~ /^\| --- \| --- \| --- \| --- \| --- \| --- \| --- \| --- \| --- \| --- \|$/) {
      printf "Source quality check failed: MODEL_MATRIX.md has a malformed capability separator at row %d\n", NR
      failed = 1
    }
    next
  }

  in_matrix && NR > header_line + 1 && /^\|/ {
    rows += 1
    if (pipe_count($0) != expected_pipes) {
      printf "Source quality check failed: MODEL_MATRIX.md capability row %d has %d columns; expected 10\n", NR, pipe_count($0) - 1
      failed = 1
    }
    next
  }

  in_matrix && NR > header_line + 1 { in_matrix = 0 }

  END {
    if (header_line == 0 || expected_pipes != 11) {
      printf "Source quality check failed: MODEL_MATRIX.md is missing its 10-column GFM capability header\n"
      failed = 1
    }
    if (header_line > 1 && source_line[header_line - 1] != "") {
      printf "Source quality check failed: MODEL_MATRIX.md capability table must start after a blank line\n"
      failed = 1
    }
    if (rows != 14) {
      printf "Source quality check failed: MODEL_MATRIX.md has %d capability rows; expected 14\n", rows
      failed = 1
    }
    exit failed
  }
' MODEL_MATRIX.md; then
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
