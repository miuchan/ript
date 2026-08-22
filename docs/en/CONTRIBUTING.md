# Contributing to Ript

[English](CONTRIBUTING.md) · [简体中文](../zh-CN/CONTRIBUTING.md) ·
[日本語](../ja/CONTRIBUTING.md) · [Esperanto](../eo/CONTRIBUTING.md)

Ript accepts proof, model, example, documentation, and tooling contributions.
Trust, explicit dependencies, reproducibility, and accurate claims are merge
requirements.

## Before starting

Read [Scope](PROJECT_SCOPE.md), [Architecture](ARCHITECTURE.md), and
[Research status](RESEARCH_STATUS.md); search issues and the
[Conjecture register](reference/CONJECTURES.md). Discuss changes to scope,
public theorem statements, architecture, trusted dependencies, governance,
security, or licensing before implementation. Security reports follow
[Security policy](SECURITY.md).

## Workflow

```bash
git switch -c <focused-branch>
lake exe cache get
lake build <affected.module>
./scripts/quality-gate.sh
```

Keep branches and commits focused. PRs must state the outcome, verification,
axiom footprint, compatibility impact, and remaining boundary. Drafts are
welcome; merge requires green CI and maintainer approval.

## Proof and implementation policy

- No proof placeholders, project axioms, trust escapes, or unsafe declarations.
- Keep `autoImplicit false`; use narrow Mathlib imports.
- Put reusable missing infrastructure in `Ript/ForMathlib/`.
- Keep executable data upstream from quotients and chosen representatives.
- Preserve capability boundaries and use domain-accurate theorem names.
- Put unfinished statements in `CONJECTURES.md`.
- Audit flagship declarations in `Ript/Audit/AxiomChecks.lean` and `AXIOMS.md`.
- Update executable assertions only for intentional, proved behavior changes.

## Documentation policy

Mirror maintained pages under all four locales. Update every affected language
when a command, claim, status, or trust boundary changes. Canonical root
blueprint, model, axiom, and conjecture records remain machine-facing sources.
Run `./scripts/sync-doc-reference-tables.sh` after axiom-table changes.

## Required gate

```bash
./scripts/quality-gate.sh
```

The gate checks source and docs policy, root imports, the full kernel build,
declaration lint, executable examples, and audited assumptions. Never weaken a
check to make a change pass.

## PR checklist

- [ ] One clear purpose and an explicit remaining boundary.
- [ ] Focused and full builds pass with the pinned toolchain.
- [ ] Flagship assumptions and executable changes are audited.
- [ ] Architecture, status, references, and all affected locales are current.
- [ ] No unrelated, generated, secret, or private files are included.

Review evaluates statements and modeling intent as well as proof terms. See
[Governance](GOVERNANCE.md) for authority and stability policy.
