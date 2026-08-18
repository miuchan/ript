# Project scope and trust

This page holds the context intentionally kept out of the repository homepage:
what Ript is designed to formalize, how its claims are checked, and which
project-level limitations apply.

## Purpose

Ordinary process theories describe which typed processes compose.
Resource-sensitive theories must additionally specify how costs compose, which
rewrites preserve them, and when syntactic estimates are semantically valid.
Ript makes those obligations explicit in Lean.

The library is organized around five principles:

- ordered additive resources track serial and parallel budgets;
- executable syntax remains separate from quotient-based proof models;
- interpretations prove preservation of typing, equations, and resource bounds;
- capabilities such as tensor, copy, discard, convexity, causality, and
  thermodynamics are represented independently;
- theorem claims are limited to declarations that compile in the pinned toolchain.

Ript is a formal research library, not a runtime estimator or a complete theory
of physical information. The exact boundary is maintained in
[Research status](RESEARCH_STATUS.md).

## What the repository contains

The formal core covers costed categories, executable sequential and monoidal
syntax, interpretations, soundness, relative completeness, and monoidal
initiality. Concrete finite models cover deterministic and stochastic channels,
decision problems, total and partial computation, causal DAGs, thermal systems,
and finite quantum channels.

Higher layers organize process models into a bicategory, define cost-exact
equivalences, study walking-localization constructions, and provide a bounded
internal identity semantics. The [model capability matrix](../MODEL_MATRIX.md)
records only implemented and compiled operations.

## Trust model

Ript forbids:

- proof placeholders such as `sorry` and `admit`;
- project-specific axioms standing in for unfinished research;
- compiler-trust escapes and unsafe library declarations;
- undocumented assumptions in audited flagship theorems.

The quality gate pins Lean and Mathlib revisions, treats warnings as errors,
executes representative models, checks source policy, audits documented
assumptions, and performs a full build. The exact assumptions of selected
theorems are recorded in [AXIOMS.md](../AXIOMS.md); open statements belong in
[CONJECTURES.md](../CONJECTURES.md).

Kernel checking establishes that a declaration follows from its listed
assumptions. It does not by itself validate whether a formal model is the right
empirical model for a physical system.

## Maturity and stability

Ript is early-stage research software:

- the Lake package version is `0.1.0`;
- there is no stable public API or tagged compatibility promise;
- there is no archival DOI;
- theorem names and module boundaries may change as the research develops.

For reproducible use, pin a full repository commit SHA. Research artifacts
should cite the repository and that SHA.

## Licensing

No open-source license has been selected. Public source availability alone does
not grant permission to copy, modify, or redistribute the code. This statement
will be replaced by the chosen license if the project adopts one.

## Authoritative records

- [Research status](RESEARCH_STATUS.md): concise proved/open boundary.
- [Formal blueprint](../BLUEPRINT.md): theorem types and dependency ledger.
- [Axiom inventory](../AXIOMS.md): audited kernel assumptions.
- [Conjecture register](../CONJECTURES.md): open research statements.
- [Contributing guide](../CONTRIBUTING.md): proof and merge policy.
