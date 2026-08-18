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
finite models with kernel-checked proofs of cost bounds, soundness,
completeness results, and structure-preserving semantics.

> [!IMPORTANT]
> Ript is early-stage research software. Its compiled results are checked by
> Lean's kernel, but the public API is not stable and the project does not claim
> a complete theory of physical information.

## Why Ript

Ordinary process theories say which processes compose. Resource-sensitive
theories must also say how costs compose, which rewrites preserve them, and
when syntactic estimates are semantically valid. Ript makes those obligations
explicit and machine-checkable.

- Ordered additive resources track serial and parallel budgets.
- Executable syntax stays separate from quotient-based proof models.
- Interpretations prove typing, equations, and resource-bound preservation.
- Optional capabilities such as tensor, copy, discard, convexity, causality,
  and thermodynamics are never inferred from one another.
- Flagship results carry an audited record of their kernel assumptions.

## Highlights

- **Formal core:** costed categories, executable sequential and monoidal
  syntax, soundness, relative completeness, and monoidal initiality.
- **Exact finite models:** deterministic, stochastic, decision,
  computational, causal, thermal, and quantum instances.
- **Higher organization:** a bicategory of process models, cost-exact
  equivalences, and checked walking-localization constructions.
- **Internal identity semantics:** axiom-free deep syntax with groupoid,
  quotient, presheaf, simplicial, and classifying-diagram interpretations.

See the [model capability matrix](MODEL_MATRIX.md) for implemented features and
the [research status](docs/RESEARCH_STATUS.md) for exact limitations.

## Quick start

Install [elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

Run the complete local CI contract before submitting changes:

```bash
./scripts/quality-gate.sh
```

To check an executable model directly:

```bash
lake env lean Ript/Examples/StochasticBits.lean
```

The [getting-started guide](docs/GETTING_STARTED.md) covers prerequisites,
examples, dependency setup, reproducibility, and troubleshooting.

## Use from Lean

Until tagged releases exist, pin a full commit SHA:

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

Prefer the smallest import that provides the required API:

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

## Documentation

- [Documentation hub](docs/README.md) — task-based routes through the project.
- [Getting started](docs/GETTING_STARTED.md) — build, run, and consume Ript.
- [Architecture](docs/ARCHITECTURE.md) — layers and dependency boundaries.
- [Research status](docs/RESEARCH_STATUS.md) — proved, active, and unclaimed.
- [Model capability matrix](MODEL_MATRIX.md) — compiled model capabilities.
- [Formal blueprint](BLUEPRINT.md) — theorem dependencies and exact status.
- [Axiom inventory](AXIOMS.md) — audited `#print axioms` output.
- [Conjecture register](CONJECTURES.md) — open research statements.
- [Contributing guide](CONTRIBUTING.md) — proof and quality policy.

## Trust, status, and governance

Ript forbids proof placeholders, project-specific axioms, compiler-trust
escapes, and unsafe library declarations. CI uses pinned Lean and Mathlib
revisions, treats warnings as errors, executes representative models, and
checks the documented axiom allowlist. Exact assumptions are recorded in
[AXIOMS.md](AXIOMS.md).

The active frontier is the arbitrary two-dimensional walking-localization
factorization. All-arrow naturality and both complete unit laws compile;
oplax associativity, pseudofunctor packaging, and the final adjoint
equivalence remain open. See
[RESEARCH_STATUS.md](docs/RESEARCH_STATUS.md) for the authoritative boundary.

The Lake package version is `0.1.0`, with no stable API release or archival DOI
yet. Research artifacts should cite the repository and exact commit SHA. No
open-source license has been selected; public source availability alone does
not grant reuse rights.

## Contributing

Contributions are welcome when claims match the compiled theorem strength and
the proof boundary is preserved. Read [CONTRIBUTING.md](CONTRIBUTING.md) and
run `./scripts/quality-gate.sh` before opening a pull request.

Ript is built with [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
