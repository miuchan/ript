# Governance

[English](GOVERNANCE.md) · [简体中文](../zh-CN/GOVERNANCE.md) ·
[日本語](../ja/GOVERNANCE.md) · [Esperanto](../eo/GOVERNANCE.md)

Ript is a maintainer-led formal research project. Decisions prioritize
mathematical accuracy, kernel-checkable evidence, explicit boundaries, and
reproducibility.

## Roles

- The maintainer owns scope, repository administration, releases, security,
  and final merge decisions.
- Contributors propose focused, reviewable proofs, models, documentation, and
  tooling.
- Reviewers evaluate theorem statements, Lean code, dependencies, audits,
  executable evidence, and public claims.

## Authority and decisions

Conflicts are resolved in this order: pinned Lean kernel acceptance; theorem
types and axiom output; canonical goal/blueprint/model/axiom/conjecture records;
then explanatory documentation. CI is necessary but does not replace
mathematical review.

Discuss scope or architecture changes first, keep pull requests focused, run
the complete quality gate, update all affected languages and audits, and keep
unfinished work in the conjecture register.

## Stability and community

There is no stable release or API guarantee; pin a commit SHA. Be precise,
constructive, and respectful. Harassment, discrimination, doxxing, credential
exposure, and misrepresentation of proof status are not accepted.

No open-source license has been selected. A license decision requires an
explicit maintainer change. See the canonical root [governance](../../GOVERNANCE.md)
and [security policy](SECURITY.md).
