# Ript

**A kernel-checked Lean 4 foundation for resource-indexed process theories.**

[English](README.md) · [简体中文](../zh-CN/README.md) ·
[日本語](../ja/README.md) · [Esperanto](../eo/README.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![Research status](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript formalizes typed processes whose behavior and resource use compose. It
connects executable finite models with kernel-checked results about resource
bounds, soundness, completeness, and structure-preserving semantics.
Its first literal six-model slice interprets one Boolean process signature in
probabilistic, quantum, causal, computational, semantic, and thermal models.

Its governing research objective is to construct a computable,
machine-verifiable, univalent, higher-categorical theory of
resource-constrained information processes in which classical probability,
quantum processes, causal models, computation, semantic information, and
thermodynamics arise as distinct models, together with representation and
completeness theorems relating those models. The repository contains the
compiled layers toward that objective; the objective as a whole is not yet a
proved theorem.

> [!IMPORTANT]
> Ript is early-stage research software. Compiled results are kernel checked;
> the public API and research frontier are still evolving.

## Get started

Install [elan](https://github.com/leanprover/elan), then build the pinned Lean
and Mathlib project:

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

For prerequisites, executable examples, dependency setup, reproducibility, and
troubleshooting, follow [Getting started](GETTING_STARTED.md).

## Find what you need

- **What is implemented?** See the
  [model capability matrix](reference/MODEL_MATRIX.md).
- **What is proved or still open?** See the
  [research status](RESEARCH_STATUS.md).
- **How is the library organized?** Read the
  [architecture guide](ARCHITECTURE.md).
- **What are the trust and maturity boundaries?** Read
  [project scope and trust](PROJECT_SCOPE.md).
- **Where are the exact research records?** Use the
  [formal blueprint](reference/BLUEPRINT.md),
  [axiom inventory](reference/AXIOMS.md), and
  [conjecture register](reference/CONJECTURES.md).

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md), then run
`./scripts/quality-gate.sh` before opening a pull request.

Ript is built with [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
