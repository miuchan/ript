# Contributing to Ript

[English](docs/en/CONTRIBUTING.md) · [简体中文](docs/zh-CN/CONTRIBUTING.md) ·
[日本語](docs/ja/CONTRIBUTING.md) · [Esperanto](docs/eo/CONTRIBUTING.md)

Ript accepts proof, model, example, documentation, and tooling contributions.
Proof trust, explicit dependencies, reproducibility, and accurate public claims
are merge requirements.

## Before starting

1. Read [Project scope](docs/en/PROJECT_SCOPE.md),
   [Architecture](docs/en/ARCHITECTURE.md), and the current
   [Research status](docs/en/RESEARCH_STATUS.md).
2. Search existing issues and `CONJECTURES.md`.
3. Open an issue before changing scope, public theorem statements, architecture,
   trusted dependencies, governance, security policy, or licensing.
4. Base work on current `main`; keep unrelated changes out of the branch.

Security-sensitive reports follow [SECURITY.md](SECURITY.md), not public issue
discussion.

## Development workflow

```bash
git switch -c <focused-branch>
lake exe cache get
lake build <affected.module>
./scripts/quality-gate.sh
```

Keep commits reviewable. A pull request should explain the mathematical or
documentation outcome, verification commands, axiom footprint, compatibility
impact, and exact remaining boundary. Draft PRs are welcome; merge requires a
green `Lean quality gate` and maintainer approval.

## Lean and proof policy

- No `sorry`, `admit`, project-specific axioms, compiler-trust escapes, or
  unsafe library declarations.
- Keep `set_option autoImplicit false` in implementation modules.
- Import the narrowest practical Mathlib modules.
- Put reusable missing infrastructure under `Ript/ForMathlib/` with a narrow
  boundary.
- Do not present finite enumeration or `#eval` as a general theorem.
- Record unproved statements in `CONJECTURES.md`; never weaken a theorem while
  retaining a stronger name.
- Add flagship declarations to `Ript/Audit/AxiomChecks.lean` and `AXIOMS.md`.

## Executable and model changes

- Keep executable finite data upstream from quotients and chosen semantic
  representatives.
- Preserve optional capability boundaries: tensor does not imply copy,
  discard, causality, convexity, thermal, dagger, or quantum structure.
- State whether a result is representation, soundness, conservativity,
  sufficiency, or completeness; do not use one generic completeness claim.
- Update `scripts/check-examples.sh` only when changed output is intentional and
  supported by the corresponding Lean declarations.

## Documentation policy

- Mirror each maintained page at the same path under `docs/en`, `docs/zh-CN`,
  `docs/ja`, and `docs/eo`.
- Update all affected languages when commands, claims, status, or trust
  boundaries change.
- Keep root `BLUEPRINT.md`, `MODEL_MATRIX.md`, `AXIOMS.md`, and
  `CONJECTURES.md` as canonical machine-facing records.
- Run `./scripts/sync-doc-reference-tables.sh` after axiom-table changes.
- Prefer task-oriented navigation and concise overview pages; durable theorem
  detail belongs in canonical references.

## Required checks

The complete pre-merge command is:

```bash
./scripts/quality-gate.sh
```

It runs source/document policy checks, root-import coverage, the full kernel
build, declaration lint, executable examples, and the axiom allowlist. Do not
weaken a check to make a change pass.

## Pull-request checklist

- [ ] The change has one clear purpose and documents its remaining boundary.
- [ ] Affected modules build with the pinned toolchain.
- [ ] `./scripts/quality-gate.sh` passes locally.
- [ ] New flagship theorems have audited and documented assumptions.
- [ ] Executable-output changes have intentional regression evidence.
- [ ] Architecture, status, model matrix, conjectures, and all languages are
      updated where applicable.
- [ ] No unrelated, generated, secret, or private files are included.

## Review and decisions

Review checks both theorem statements and proofs; kernel acceptance alone does
not validate modeling intent. The maintainer may request narrower scope,
additional examples, a theorem rename, an explicit conjecture, or specialist
review. See [GOVERNANCE.md](GOVERNANCE.md) for decision authority and stability.
