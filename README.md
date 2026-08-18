# Ript

**A kernel-checked Lean 4 foundation for resource-indexed process theories.**

[English](README.md) · [简体中文](docs/README.zh-CN.md) ·
[日本語](docs/README.ja.md) · [Esperanto](docs/README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![Research status](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript formalizes **Resource-Indexed Information Process Theory**: typed
processes whose behavior and resource use compose. It connects executable
finite models with kernel-checked proofs of resource bounds, soundness,
completeness results, and structure-preserving semantics.

> [!IMPORTANT]
> Ript is early-stage research software. Compiled results are kernel checked;
> the public API and the research frontier are still evolving.

## What is included

- **Formal foundations:** costed categories, executable syntax, interpretations,
  soundness, relative completeness, and monoidal initiality.
- **Exact finite models:** deterministic, stochastic, decision, computational,
  causal, thermal, and quantum instances.
- **Higher structures:** a bicategory of process models, cost-exact
  equivalences, and walking-localization constructions.
- **Auditable proofs:** CI rejects placeholders and undocumented assumptions;
  flagship theorems have an explicit axiom inventory.

Implemented capabilities are listed in the
[model matrix](MODEL_MATRIX.md). Precise proved, open, and unclaimed results
are separated in the [research status](docs/RESEARCH_STATUS.md).

## Quick start

Install [elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

Verify the full local CI contract with:

```bash
./scripts/quality-gate.sh
```

To consume the library before tagged releases, pin a full commit SHA:

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

See [Getting started](docs/GETTING_STARTED.md) for prerequisites, examples,
dependency setup, and troubleshooting.

## Documentation

- [Documentation hub](docs/README.md) — choose the shortest path for your task.
- [Project scope and trust](docs/PROJECT_SCOPE.md) — design, claims, proof
  policy, maturity, citation, and licensing.
- [Architecture](docs/ARCHITECTURE.md) — layers and dependency boundaries.
- [Research status](docs/RESEARCH_STATUS.md) — implemented, active, and open.
- [Formal blueprint](BLUEPRINT.md) · [Axiom inventory](AXIOMS.md) ·
  [Conjecture register](CONJECTURES.md) — authoritative research ledgers.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md), then run
`./scripts/quality-gate.sh` before opening a pull request.

Ript is built with [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
