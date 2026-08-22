# Ript documentation

[English](README.md) · [简体中文](../zh-CN/README.md) ·
[日本語](../ja/README.md) · [Esperanto](../eo/README.md)

Ript is a kernel-checked Lean 4 research library for resource-indexed
information processes. It connects executable finite syntax with
probabilistic, quantum, causal, computational, semantic-information, decision,
and thermodynamic models while keeping optional capabilities separate.

> [!IMPORTANT]
> The repository contains substantial proved infrastructure, but remains
> early-stage research. The final global theorem and a stable API are open.

## Current snapshot

- exact resource-sensitive syntax, budgets, soundness, relative completeness,
  and free semantics compile;
- all six model families have concrete instances and checked nontrivial
  examples;
- models and resource-changing morphisms form verified bicategorical layers;
- internally univalent and complete-Segal foundations are downstream of the
  executable core;
- generated hammock mapping spaces are equivalent to the actual localization
  targets, with explicit nerve homotopy inverses and terminating reductions.

The current frontier is critical-pair joinability, classical reduced-hammock
invariance, standard weak-equivalence packaging, and the global Rezk theorem.

## Start here

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
./scripts/quality-gate.sh
```

Continue with [Getting started](GETTING_STARTED.md).

## Read by task

- **Understand the project:** [Scope and trust](PROJECT_SCOPE.md) ·
  [Architecture](ARCHITECTURE.md)
- **See what is proved:** [Research status](RESEARCH_STATUS.md) ·
  [Model matrix](reference/MODEL_MATRIX.md)
- **Audit exact evidence:** [Blueprint](reference/BLUEPRINT.md) ·
  [Axioms](reference/AXIOMS.md) · [Conjectures](reference/CONJECTURES.md)
- **Participate:** [Contributing](CONTRIBUTING.md) ·
  [Governance](GOVERNANCE.md) · [Security](SECURITY.md)
- **Switch language:** [Multilingual documentation hub](../README.md)

## Maturity and reuse

Use a full commit SHA for reproducibility. There are no stable releases or API
compatibility guarantees. No open-source license has been selected, so public
source availability does not grant reuse rights; see
[Project scope](PROJECT_SCOPE.md#licensing).
