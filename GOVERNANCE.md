# Governance

[English](docs/en/GOVERNANCE.md) · [简体中文](docs/zh-CN/GOVERNANCE.md) ·
[日本語](docs/ja/GOVERNANCE.md) · [Esperanto](docs/eo/GOVERNANCE.md)

Ript is a maintainer-led formal research project. Governance is optimized for
mathematical accuracy, kernel-checkable evidence, explicit scope boundaries,
and reproducible decisions.

## Roles

- **Maintainer:** owns repository administration, scope, releases, security
  coordination, and final merge decisions.
- **Contributor:** proposes issues, proofs, models, documentation, or tooling
  through reviewable changes and follows the trust and quality policies.
- **Reviewer:** evaluates mathematical statements, Lean implementation,
  dependencies, audits, executable evidence, and public claims. Review is a
  responsibility, not a permanent title.

The current repository owner is listed on the
[GitHub project](https://github.com/miuchan/ript).

## Decision order

When evidence conflicts, decisions follow this order:

1. Lean kernel acceptance under the pinned toolchain;
2. explicit theorem types and `#print axioms` output;
3. canonical records: `RESEARCH_GOAL.md`, `BLUEPRINT.md`, `MODEL_MATRIX.md`,
   `AXIOMS.md`, and `CONJECTURES.md`;
4. architecture, research-status, examples, and other explanatory prose.

Passing CI is necessary but does not prove that a theorem states the intended
mathematics. Review must check both the statement and its evidence.

## Change process

- Discuss scope-changing or architecture-changing work in an issue first.
- Keep pull requests focused and state proved, executable, and open boundaries.
- Require the complete quality gate and green protected CI before merge.
- Record new flagship assumptions and update every affected language.
- Use conjecture records instead of weakening a theorem or adding an axiom.

The maintainer may request additional review for changes to the trusted core,
public theorem statements, model semantics, security policy, or licensing.

## Releases and compatibility

There is no stable release train or compatibility guarantee. Reproducible
research must pin a commit SHA. A future release policy must define API
stability, migration notes, archival identifiers, and support windows before a
version is called stable.

## Community standards

Be precise, constructive, and respectful. Critique statements and evidence,
not people. Harassment, discrimination, doxxing, credential exposure, and
deliberate misrepresentation of proof status are not accepted. Conduct or
security-sensitive concerns should use the private path in `SECURITY.md` when
possible.

## Licensing boundary

No open-source license has been selected. Governance and contribution do not
themselves grant reuse rights. Selecting or changing a license requires an
explicit maintainer decision and a dedicated repository change.
