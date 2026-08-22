# Getting started

[English](GETTING_STARTED.md) · [简体中文](../zh-CN/GETTING_STARTED.md) ·
[日本語](../ja/GETTING_STARTED.md) · [Esperanto](../eo/GETTING_STARTED.md)

This guide takes a fresh checkout from toolchain installation to a verified
build, then points to representative executable models.

## Prerequisites

Install:

- Git;
- a POSIX-compatible shell;
- [elan](https://github.com/leanprover/elan), the Lean toolchain manager.

The repository pins Lean in `lean-toolchain` and Mathlib in `lakefile.lean` and
`lake-manifest.json`. Do not substitute a globally installed Lean version.

## Clone and build

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

`lake exe cache get` downloads matching precompiled Mathlib artifacts when they
are available. `lake build` then compiles the complete `Ript` library with Lean
warnings promoted to errors.

## Run the quality gate

```bash
./scripts/quality-gate.sh
```

The gate runs, in order:

1. source-policy and documentation checks;
2. root-module coverage verification;
3. a complete kernel build;
4. declaration lint;
5. executable example assertions;
6. the kernel-assumption allowlist.

For a focused iteration, the individual commands are:

```bash
./scripts/check-source-quality.sh
lake exe mk_all --check
lake build
lake env lean Ript/Audit/Lint.lean
./scripts/check-examples.sh
./scripts/check-axioms.sh
```

The complete gate is still required before a pull request is ready to merge.

## Explore executable examples

Every example below is a normal Lean module: running it checks all declarations
and prints any `#eval` results.

Core resources and functions:

```bash
lake env lean Ript/Examples/BitProcesses.lean
lake env lean Ript/Examples/CostFiltration.lean
lake env lean Ript/Examples/ClassicalCopy.lean
```

Exact stochastic and decision models:

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/KleisliBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/StochasticSeparation.lean
```

Computation and causality:

```bash
lake env lean Ript/Examples/SimpleComputation.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

Thermodynamics:

```bash
lake env lean Ript/Examples/SimpleThermalModel.lean
lake env lean Ript/Examples/ApproximateErasure.lean
lake env lean Ript/Examples/ExactWorkCycle.lean
```

Quantum and internally univalent semantics:

```bash
lake env lean Ript/Examples/QubitChannel.lean
lake env lean Ript/Examples/UnivalentProcessUniverse.lean
lake env lean Ript/Examples/UnivalentSimplicial.lean
```

The expected outputs are enforced by `scripts/check-examples.sh`; examples are
not merely prose snippets.

## Use Ript as a dependency

Ript does not yet publish stable tagged releases. Pin a complete commit SHA:

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

After changing `lakefile.lean`, run:

```bash
lake update ript
lake exe cache get
lake build
```

Prefer narrow imports:

```lean
import Ript.Resource.Budget
import Ript.Core.CostedProcess
import Ript.Models.FiniteStochastic
```

The umbrella `import Ript` is convenient for exploration but intentionally
larger.

## Reproducible research use

Record all of the following in an artifact:

- the full Ript commit SHA;
- the `lean-toolchain` contents;
- the Mathlib revision from `lake-manifest.json`;
- the exact validation command;
- any theorem's audited assumptions from `AXIOMS.md`.

The package version alone is not sufficient while the API remains unstable.

## Troubleshooting

### Lean version mismatch

Run `elan show` in the repository root. Elan should select the toolchain named
by `lean-toolchain`. If it does not, repair the elan installation before
changing repository files.

### Missing compiled Mathlib artifacts

Run `lake exe cache get` again. If a cache is unavailable for the platform,
`lake build` can compile dependencies locally, which takes longer.

### A root-module coverage failure

Every public implementation module must be imported by `Ript.lean`. Add the
narrow import there, then rerun `lake exe mk_all --check`.

### An axiom allowlist failure

Do not weaken the script. Run the relevant `#print axioms` command, determine
whether the dependency is expected, and update both
`Ript/Audit/AxiomChecks.lean` and `AXIOMS.md` only when the theorem and its
documented trust boundary genuinely changed.

### An executable example changed

Inspect the semantic change first. Update `scripts/check-examples.sh` only when
the new output is intentional and proved by the corresponding example module.

## Next reading

- [Architecture](ARCHITECTURE.md) for module and dependency boundaries.
- [Research status](RESEARCH_STATUS.md) for the current mathematical frontier.
- [Formal blueprint](reference/BLUEPRINT.md) for theorem-level status.
- [Contributing](CONTRIBUTING.md) for the development and review workflow.
- [Governance](GOVERNANCE.md) and [Security](SECURITY.md) for project policy.
