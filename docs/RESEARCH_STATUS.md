# Research status

This page is a concise research map, not the theorem ledger. Exact theorem
types, dependencies, source files, and assumptions live in
[`BLUEPRINT.md`](../BLUEPRINT.md) and [`AXIOMS.md`](../AXIOMS.md).

## Status vocabulary

Ript uses only these formal status labels in the blueprint:

- `DEFINED` — an interface or construction exists;
- `STATEMENT_FORMALIZED` — a theorem type exists but no proved declaration is
  claimed;
- `PROVED` — Lean accepts the proof without project axioms or placeholders;
- `BLOCKED` — a specific dependency or API gap is recorded;
- `OPEN_RESEARCH` — the statement or correct formulation remains research.

The README and model matrix summarize only implemented, compiled work.

## Implemented pillars

### Resource-sensitive syntax and semantics

The sequential and symmetric monoidal cores include executable syntax, syntax
cost, interpretations, explicit derivations, soundness, term models, relative
completeness, and monoidal initiality. Cost functions and attained budget
filtrations have proved round-trip laws under explicit hypotheses.

### Exact finite probability and decisions

Normalized rational stochastic channels form a category with tensor, convex
mixtures, copy, and discard. The finite-distribution Kleisli representation and
a faithful finite-discrete bridge to Mathlib `Stoch` compile. The decision layer
contains forward Blackwell monotonicity and finite converse results with the
necessary nonempty hidden-state boundary, plus exact separator certificates.

### Causal, computational, and thermal models

Finite DAG causal models have normalized observational semantics and hard
interventions. Total and `Option`-partial computation models track formal
steps, queries, storage, and gate counts. Finite Gibbs-preserving models connect
exact rational operations to KL, free-energy, correlation, approximate erasure,
and explicit Landauer witnesses under stated analytic hypotheses.

### Finite quantum channels

Finite Kraus families define channels only after positivity and trace
preservation are proved. Identity, composition, tensor, trace discard, complete
positivity under finite amplification, and a faithful classical dephasing
embedding compile. No universal quantum copying operation is claimed.

### Models as higher objects

Resource-indexed symmetric monoidal process models, resource-nonincreasing
strong braided monoidal functors, and monoidal natural transformations form a
bicategory. Cost-exact equivalences add explicit numerical reflection. An
ordinary homotopy localization and multiple walking-localization test cases
compile.

### A bounded internal univalent layer

Deep syntax distinguishes internal identity from structural equivalence and
interprets both without adding external axioms. The compiled semantics include
a groupoid, object quotient, skeleton, Yoneda envelope, Kan simplicial nerve,
and a classifying diagram satisfying the project's explicit groupoidal
complete-Segal interface.

## Active frontier

The immediate target is the arbitrary marking-inverting pseudofunctor out of
the two-dimensional walking source.

Already compiled:

- action on all target objects, 1-morphisms, and 2-morphisms;
- identity comparisons for all objects;
- composition comparisons for all composable arrows;
- endpoint-normalized formulas for all eight endpoint triples;
- forward, mixed, and cancellation compositor naturality;
- all-arrow left and right naturality after thinness normalization;
- source and target unit factorizations;
- complete oplax left- and right-unit coherence for every target arrow,
  including the freely adjoined inverse.

Still required:

- oplax associativity coherence;
- packaging as an oplax functor and then a pseudofunctor;
- an adjoint equivalence identifying source restriction with the original
  marking-inverting pseudofunctor;
- the resulting arbitrary, nonseparable biessential-factorization field.

Until those steps compile, the parameterized walking construction is not
described as a complete bicategorical localization.

## Explicitly open or out of scope

- general measurable-space causal models and do-calculus completeness;
- a claim that formal step counts equal wall-clock runtime or hardware cost;
- irrational real probabilities in the executable finite stochastic core;
- a universal quantum copy operation;
- external univalence for Lean types;
- a Mathlib-native standard complete-Segal-space object using a completed
  weak-equivalence or Quillen-model API;
- a full Dwyer–Kan, simplicial, Rezk, or bicategorical localization theorem for
  the resource-process bicategory.

Open statements belong in [`CONJECTURES.md`](../CONJECTURES.md), not in Lean as
axioms or theorem declarations.

## Where to verify a claim

- Model operation or capability: [`MODEL_MATRIX.md`](../MODEL_MATRIX.md)
- Theorem type and dependencies: [`BLUEPRINT.md`](../BLUEPRINT.md)
- Kernel assumptions: [`AXIOMS.md`](../AXIOMS.md)
- Open research statement: [`CONJECTURES.md`](../CONJECTURES.md)
- Executable behavior: `Ript/Examples/` and `scripts/check-examples.sh`
- Merge readiness: `./scripts/quality-gate.sh`

This separation keeps the repository homepage readable while preserving the
full, auditable detail needed for formal research.
