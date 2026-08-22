# Ript

**Kernel-checked foundations for resource-indexed information processes.**

[English](docs/en/README.md) · [简体中文](docs/zh-CN/README.md) ·
[日本語](docs/ja/README.md) · [Esperanto](docs/eo/README.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![Status](https://img.shields.io/badge/status-early--stage%20research-orange)
![License](https://img.shields.io/badge/license-not%20selected-lightgrey)

Ript is a Lean 4 research library for typed processes whose behavior and
resource use compose. It keeps executable finite syntax separate from
quotient-based semantic layers and connects classical probability, quantum
processes, causal models, computation, task-relative semantic information,
and thermodynamics through structure-preserving interpretations.

> [!IMPORTANT]
> Ript is early-stage research software. Kernel-checked declarations are real
> proofs, but the public API and the global research theorem are not complete.

## Verified today

- executable sequential, monoidal, adaptive, dependent, and parallel syntax
  with exact costs and budgets;
- soundness, term-model relative completeness, free/initial semantics, and
  several model-specific representation or completeness theorems;
- concrete finite probabilistic, quantum, causal, computational, semantic,
  decision, and thermodynamic models with nontrivial executable examples;
- a total resource-model bicategory and internally interpreted univalent,
  simplicial, and complete-Segal foundations;
- a full generated-hammock mapping-space presentation, direct target nerve
  equivalences, and a terminating semantics-preserving reduction layer.

The active frontier is raw critical-pair joinability, classical reduced
hammock invariance, a standard weak-equivalence interface, and the final global
Dwyer--Kan/Rezk theorem. See [Research status](docs/en/RESEARCH_STATUS.md).

## Quick start

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
./scripts/quality-gate.sh
```

The repository pins Lean and Mathlib. Follow [Getting started](docs/en/GETTING_STARTED.md)
for prerequisites, focused commands, examples, dependency use, and troubleshooting.

## Documentation

- **Learn the system:** [Project scope](docs/en/PROJECT_SCOPE.md) ·
  [Architecture](docs/en/ARCHITECTURE.md)
- **Inspect current evidence:** [Research status](docs/en/RESEARCH_STATUS.md) ·
  [Model matrix](docs/en/reference/MODEL_MATRIX.md)
- **Audit exact claims:** [Blueprint](docs/en/reference/BLUEPRINT.md) ·
  [Axioms](docs/en/reference/AXIOMS.md) ·
  [Conjectures](docs/en/reference/CONJECTURES.md)
- **Work on Ript:** [Contributing](CONTRIBUTING.md) · [Governance](GOVERNANCE.md) ·
  [Security](SECURITY.md)
- **Choose another language:** [Documentation hub](docs/README.md)

## Reuse and citation

Pin a full commit SHA for reproducible research and record the audited theorem
assumptions. No open-source license has been selected: public availability does
not currently grant permission to copy, modify, or redistribute the code. See
[Project scope and trust](docs/en/PROJECT_SCOPE.md) for the exact boundary.
