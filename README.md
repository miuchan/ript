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
models with kernel-checked proofs of cost bounds, soundness, relative
completeness, and structure-preserving semantics.

> [!IMPORTANT]
> Ript is early-stage research software. Its compiled results are checked by
> Lean's kernel, but the public API is not stable and the project does not claim
> to be a complete theory of physical information.

## Why Ript?

Ordinary process theories describe which processes compose. Resource-sensitive
theories must also explain how composition costs, which rewrites preserve that
cost, and when a syntactic estimate is semantically valid.

Ript makes those obligations explicit:

- resources form an ordered additive algebra;
- serial and parallel composition carry proved upper bounds;
- executable syntax is separate from quotient-based proof models;
- interpretations preserve typing, equations, and declared resource bounds;
- concrete deterministic, stochastic, computational, causal, thermal, and
  quantum models instantiate the generic interfaces;
- every flagship theorem has a recorded kernel-assumption audit.

The name **Ript** abbreviates **Resource-Indexed Information Process Theory**.

## What is implemented

The current library includes four connected layers.

### Formal core

- ordered additive resources, budgets, monotonicity, and cost filtrations;
- costed categories with serial and parallel composition;
- executable sequential and symmetric monoidal syntax;
- explicit equational derivations, soundness, term models, relative
  completeness, and monoidal initiality.

### Exact finite models

- finite functions and metered total/partial computation;
- exact finite stochastic channels over nonnegative rationals;
- a finite-distribution Kleisli representation and faithful `Stoch` bridge;
- Blackwell comparison, exact finite Bayes risk, and task-relative semantic
  value;
- finite DAG causal models with normalized hard interventions;
- finite Gibbs-preserving systems, KL/free-energy results, and executable
  Landauer witnesses;
- finite-dimensional Kraus channels and a faithful classical dephasing
  embedding.

### Higher organization

- a bicategory of resource-indexed symmetric monoidal process models;
- cost-exact model equivalences and an ordinary homotopy localization;
- nontrivial walking-localization test cases, including a two-dimensional
  parameterized construction.

### Internal univalent boundary

- an axiom-free deep syntax for internal identity and structural equivalence;
- groupoid, quotient, presheaf, simplicial nerve, and classifying-diagram
  semantics;
- explicitly bounded 0/1-truncated results, without assuming external
  univalence or equating arbitrary Lean equivalences with Lean equality.

For exact capability claims, limitations, and theorem status, use the
[model matrix](MODEL_MATRIX.md), [research status](docs/RESEARCH_STATUS.md), and
[formal blueprint](BLUEPRINT.md). Those documents are authoritative; this page
is intentionally an overview.

## Quick start

### Requirements

- Git
- a POSIX shell
- [elan](https://github.com/leanprover/elan), which installs the pinned Lean
  toolchain automatically

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

Run every repository gate before submitting a change:

```bash
./scripts/quality-gate.sh
```

The gate checks source policy, root-module coverage, a warning-free kernel
build, declaration lint, executable examples, and the axiom allowlist.

## Try an executable model

The examples are ordinary Lean modules. For example:

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

Each command both checks its proofs and evaluates its finite examples. See the
[getting-started guide](docs/GETTING_STARTED.md) for the full example map,
individual validation commands, and troubleshooting.

## Use Ript from Lean

Until tagged releases exist, pin a full commit SHA:

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

Then import the smallest module that provides the API you need, for example:

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

`import Ript` is available for exploration, but narrow imports make dependency
boundaries clearer and builds more predictable.

## Documentation

- [Documentation hub](docs/README.md) — choose the shortest path for your task.
- [Getting started](docs/GETTING_STARTED.md) — setup, examples, dependency use,
  and troubleshooting.
- [Architecture](docs/ARCHITECTURE.md) — layers, dependency direction, and
  executable/proof boundaries.
- [Research status](docs/RESEARCH_STATUS.md) — implemented pillars, active
  frontier, and deliberately unclaimed results.
- [Model capability matrix](MODEL_MATRIX.md) — implemented capabilities only.
- [Formal blueprint](BLUEPRINT.md) — theorem dependency graph and exact status.
- [Axiom inventory](AXIOMS.md) — audited `#print axioms` output.
- [Conjecture register](CONJECTURES.md) — open and recently discharged research
  statements.
- [Contributing guide](CONTRIBUTING.md) — mandatory proof and quality policy.

## Repository map

```text
Ript/Resource/    resource algebras, budgets, and filtrations
Ript/Core/        costed process interfaces and capabilities
Ript/Syntax/      executable sequential and monoidal syntax
Ript/Semantics/   interpretation, soundness, completeness, initiality
Ript/Models/      deterministic, stochastic, decision, causal, thermal, quantum
Ript/Higher/      model morphisms, bicategory, coherence, localization
Ript/Univalent/   downstream deep syntax and 0/1-truncated semantics
Ript/Examples/    checked, often executable end-to-end examples
Ript/Audit/       linter and kernel-assumption audit entry points
```

The dependency direction is deliberate:

```text
Executable core  →  Semantic models  →  Higher organization
                                  ↘  Internal univalent interpretation
```

The downstream layers never add axioms to the executable core.

## Trust and reproducibility

Ript forbids proof placeholders, project-specific axioms, compiler-trust
escapes, unsafe declarations, and broad umbrella imports in library modules.
CI rebuilds the project with the pinned Lean and Mathlib revisions and treats
warnings as errors.

Some audited theorems use standard Mathlib foundations such as quotient
soundness, propositional extensionality, or classical choice. Their exact
dependencies are recorded in [AXIOMS.md](AXIOMS.md); no theorem is described as
constructive merely because its statement concerns finite data.

## Current frontier

The active higher-categorical frontier is the arbitrary, nonseparable
two-dimensional walking-localization factorization. Its object, morphism,
2-morphism, identity-comparison, composition-comparison, and all-arrow
naturality data compile. The left-unit equation also compiles on every
canonical forward target arrow. Its reverse-arrow branch, the full right-unit
law, oplax associativity coherence, pseudofunctor packaging, and the resulting
adjoint-equivalence factorization remain open.

Other intentionally open directions include general measurable causal models,
a Mathlib-native complete-Segal-space interface with weak equivalences, and a
full bicategorical or Dwyer–Kan localization theorem. See
[RESEARCH_STATUS.md](docs/RESEARCH_STATUS.md) for precise boundaries.

## Contributing

Contributions are welcome when they preserve the project's proof boundary and
state claims at exactly the strength proved. Start with
[CONTRIBUTING.md](CONTRIBUTING.md), run `./scripts/quality-gate.sh`, and update
the blueprint and axiom inventory when a flagship theorem changes.

## Versioning, citation, and license

The Lake package version is `0.1.0`. There is no stable API release yet, so
research artifacts should record the exact commit SHA they use.

Ript has no archival paper or DOI yet. Cite the repository URL and pinned commit
for reproducibility.

No open-source license has been selected yet. Public source availability does
not grant permission to copy, redistribute, or create derivative works until a
license file is added.

## Acknowledgements

Ript is built with [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4). Their proof,
algebra, category-theory, and tooling ecosystems make this work possible.
