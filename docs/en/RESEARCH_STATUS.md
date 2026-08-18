# Research status

[English](RESEARCH_STATUS.md) · [简体中文](../zh-CN/RESEARCH_STATUS.md) ·
[日本語](../ja/RESEARCH_STATUS.md) · [Esperanto](../eo/RESEARCH_STATUS.md)

This page is a concise research map, not the theorem ledger. Exact theorem
types, dependencies, source files, and assumptions live in
[`BLUEPRINT.md`](reference/BLUEPRINT.md) and [`AXIOMS.md`](reference/AXIOMS.md).

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
The same monoidal language can now be pushed along an ordered additive
resource map without changing its wires or generators. Expression translation
is computably invertible, heterogeneous interpretations are represented
exactly by ordinary interpretations of the pushed signature, evaluation obeys
the translated budget, and the pushed free model is relatively complete with
an exact translated cost.

The first concrete cross-model slice now compiles as well. One unit-cost
Boolean-flip signature is interpreted by exact probability, Pauli-X quantum
evolution, a finite causal mechanism, multidimensional computation,
task-relative semantic information, and a Gibbs-preserving thermal process.
The six observable boundary equations are packaged by one checked theorem.
Computation retains its native vector resource, while quantum and thermal
analytic observables remain separate from this slice's zero abstract cost.

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

Resource algebras no longer have to be globally identical merely to compare
models. Ordered additive homomorphisms reindex serial, parallel, structural,
and budget laws. Strong braided model morphisms across different resource
algebras compose together with those homomorphisms, and monoidal natural
transformations form the local categories over each fixed resource map. A
four-dimensional computation cost now has an executable, theorem-backed
projection to its `Nat` step count. These fibres are now assembled into a
single total bicategory: objects bundle their resource algebra and process
model, 1-cells carry the resource translation and strong model morphism, and
2-cells retain equality of the resource translation together with a monoidal
natural transformation. Horizontal composition, interchange, associators,
unitors, pentagon, and triangle compile. A vector-valued free process model
and its step-count reindexing provide an executable heterogeneous 1-cell.

### A bounded internal univalent layer

Deep syntax distinguishes internal identity from structural equivalence and
interprets both without adding external axioms. The compiled semantics include
a groupoid, object quotient, skeleton, Yoneda envelope, Kan simplicial nerve,
and a classifying diagram satisfying the project's explicit groupoidal
complete-Segal interface.

## Active frontier

The governing objective is a computable, machine-verifiable, univalent,
higher-categorical theory of resource-constrained information processes whose
classical probabilistic, quantum, causal, computational, semantic, and
thermodynamic realizations are connected by proved representation and
completeness theorems.

The first total higher category over varying resource algebras now compiles.
Its verified components are:

- ordered-additive resource reindexing for process, parallel, structural, and
  proof-carrying budget laws;
- resource-changing functors, identity-resource compatibility, composition,
  and budget transport;
- reindexed `ProcessModel` objects and heterogeneous strong braided model
  morphisms whose resource translations compose;
- monoidal 2-cells and vertical local categories over each fixed resource
  translation;
- total resource-model objects, heterogeneous horizontal composition and
  whiskering, interchange, associators, unitors, pentagon, and triangle;
- a common monoidal syntax whose costs can be translated into each model's
  native resource algebra, with reversible expression translation, an exact
  interpretation representation theorem, and translated free-model
  completeness;
- one literal Boolean-flip process signature with six model-specific
  interpretations and a kernel-checked cross-model agreement theorem;
- an executable projection from `Fin 4 → Nat` computation resources to the
  single `Nat` step coordinate, upgraded to a model-level 1-cell with checked
  budget transport.

The next theorem-bearing layers are:

- extend the first six-model Boolean slice to a common compositional signature
  rich enough to expose probability, causal, semantic, quantum, and thermal
  distinctions, with explicit analytic and finite-boundary hypotheses;
- formulate and prove model-specific representation, conservativity, and
  completeness theorems, followed by genuinely cross-model comparison
  theorems;
- connect the total model bicategory to the internal univalent and simplicial
  semantics without feeding noncomputable quotient choices into executable
  models.

The parameterized walking-localization construction remains an active
supporting track. Its arbitrary lift has compiled object, 1-cell, 2-cell,
identity, compositor, naturality, unit, forward associativity, and one
inverse/retained/retained associativity branch. Ten inverse or cancellation
endpoint sequences, pseudofunctor packaging, and the final nonseparable
biessential factorization remain open; consequently no full bicategorical
localization is claimed.

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

Open statements belong in [`CONJECTURES.md`](reference/CONJECTURES.md), not in Lean as
axioms or theorem declarations.

## Where to verify a claim

- Model operation or capability: [`MODEL_MATRIX.md`](reference/MODEL_MATRIX.md)
- Theorem type and dependencies: [`BLUEPRINT.md`](reference/BLUEPRINT.md)
- Kernel assumptions: [`AXIOMS.md`](reference/AXIOMS.md)
- Open research statement: [`CONJECTURES.md`](reference/CONJECTURES.md)
- Executable behavior: `Ript/Examples/` and `scripts/check-examples.sh`
- Merge readiness: `./scripts/quality-gate.sh`

This separation keeps the repository homepage readable while preserving the
full, auditable detail needed for formal research.
