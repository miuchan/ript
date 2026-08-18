# Ript documentation

This directory contains task-focused documentation. The repository root keeps
the formal status registers because they are updated alongside theorem changes.

## Choose a path

- **I want to build or try Ript.** Read [Getting started](GETTING_STARTED.md).
- **I want to understand the module boundaries.** Read
  [Architecture](ARCHITECTURE.md).
- **I want to know what is proved today.** Read
  [Research status](RESEARCH_STATUS.md), then the
  [model capability matrix](../MODEL_MATRIX.md).
- **I need an exact theorem record.** Use the
  [formal blueprint](../BLUEPRINT.md).
- **I need kernel assumptions.** Use the audited
  [axiom inventory](../AXIOMS.md).
- **I want to contribute.** Start with
  [CONTRIBUTING.md](../CONTRIBUTING.md).

## Project documentation

- [Getting started](GETTING_STARTED.md) covers prerequisites, builds,
  executable examples, dependency use, reproducibility, and troubleshooting.
- [Architecture](ARCHITECTURE.md) explains the dependency graph, the executable
  versus semantic boundary, and the higher/univalent layers.
- [Research status](RESEARCH_STATUS.md) summarizes the implemented pillars,
  current frontier, and results that are deliberately not claimed.
- [Model capability matrix](../MODEL_MATRIX.md) records only implemented and
  compiled capabilities.
- [Formal blueprint](../BLUEPRINT.md) is the detailed theorem and dependency
  ledger.
- [Axiom inventory](../AXIOMS.md) records checked `#print axioms` results.
- [Conjecture register](../CONJECTURES.md) separates open research statements
  from proved library declarations.
- [Contributing guide](../CONTRIBUTING.md) defines the mandatory proof and CI
  policy.

## Translated project overviews

- [English](../README.md)
- [简体中文](README.zh-CN.md)
- [日本語](README.ja.md)
- [Esperanto](README.eo.md)

The translated pages are concise project entry points. Detailed technical
documentation is maintained in English as a single source of truth; Lean
declarations and the formal status registers remain the authoritative record.
