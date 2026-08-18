# Ript

**A kernel-checked Lean 4 foundation for resource-indexed process theories.**

[English](README.md) · [简体中文](docs/README.zh-CN.md) ·
[日本語](docs/README.ja.md) · [Esperanto](docs/README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![Research status](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript formalizes typed processes whose behavior and resource use compose. It
connects executable finite models with kernel-checked results about resource
bounds, soundness, completeness, and structure-preserving semantics.

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
troubleshooting, follow [Getting started](docs/GETTING_STARTED.md).

## Find what you need

- **What is implemented?** See the [model capability matrix](MODEL_MATRIX.md).
- **What is proved or still open?** See the
  [research status](docs/RESEARCH_STATUS.md).
- **How is the library organized?** Read the
  [architecture guide](docs/ARCHITECTURE.md).
- **What are the trust and maturity boundaries?** Read
  [project scope and trust](docs/PROJECT_SCOPE.md).
- **Where are the exact research records?** Use the
  [formal blueprint](BLUEPRINT.md), [axiom inventory](AXIOMS.md), and
  [conjecture register](CONJECTURES.md).
- **Not sure where to begin?** Open the [documentation hub](docs/README.md).

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md), then run
`./scripts/quality-gate.sh` before opening a pull request.

Ript is built with [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
