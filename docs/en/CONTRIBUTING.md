# Contributing to Ript

[English](CONTRIBUTING.md) · [简体中文](../zh-CN/CONTRIBUTING.md) ·
[日本語](../ja/CONTRIBUTING.md) · [Esperanto](../eo/CONTRIBUTING.md)

Ript treats proof trust, explicit dependencies, and reproducible computation as
merge requirements rather than review conventions.

## Required quality gate

Run the complete gate from the repository root before opening a pull request:

```bash
./scripts/quality-gate.sh
```

The gate rejects proof placeholders, project-specific axioms, unsafe
declarations, compiler-trust escapes, broad `Mathlib` imports, implicit Lean
identifiers, stale root-module imports, declaration-linter failures, executable
behavior changes, build warnings, and undocumented theorem assumptions. It then
performs a full kernel build.

CI exposes these checks as the stable `Lean quality gate` job. A change is ready
to merge only when that job passes.

## Proof and dependency policy

- Put unproved research statements in `CONJECTURES.md`; do not declare them as
  theorems or axioms.
- Import the narrowest practical Mathlib modules.
- Keep `set_option autoImplicit false` in every implementation module.
- Add flagship theorems to both `Ript/Audit/AxiomChecks.lean` and `AXIOMS.md`.
- If executable behavior changes intentionally, update the example assertion in
  `scripts/check-examples.sh` in the same change.

## Documentation policy

- Keep every logical page mirrored under `docs/en`, `docs/zh-CN`, `docs/ja`,
  and `docs/eo` with the same relative path.
- Update all four language versions when a public claim, command, status, or
  trust boundary changes.
- Keep root `AXIOMS.md`, `BLUEPRINT.md`, `CONJECTURES.md`, and
  `MODEL_MATRIX.md` as the machine-facing canonical records.
- After changing the axiom inventory, run
  `./scripts/sync-doc-reference-tables.sh` before the quality gate.
