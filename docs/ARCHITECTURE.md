# Architecture

Ript is organized so that executable finite models do not depend on quotient,
measure-theoretic, higher-categorical, or internally univalent machinery. Each
layer may use the interfaces below it; reverse imports are intentionally
forbidden by review and root-module structure.

## Dependency direction

```text
Resource algebra
      ↓
Costed process interfaces
      ↓
Resource reindexing and heterogeneous model maps
      ↓
Executable syntax ──→ Semantics and term models
      ↓                        ↓
Finite models ───────→ General semantic bridges
      ↓                        ↓
Model bicategory and localization
      ↓
Internal univalent interpretation
```

The last layer interprets a deep syntax. It does not alter Lean equality or add
univalence to the layers above it.

## Resource and process core

`Ript/Resource/` defines the algebra used to measure processes:

- ordered additive resources;
- budgets and budgeted morphisms;
- monotone transport and ordered-additive change of resource algebra;
- cost-induced and attained filtrations;
- parallel-budget laws.

`Ript/Core/` connects that algebra to categories and capabilities:

- process cost and serial subadditivity;
- optional parallel cost, structural cost, convexity, copy, and discard;
- simulations and monotone maps;
- capability interfaces that do not infer extra structure.

Tensor does not imply copying or discarding. Convexity, causal structure, and
thermal structure are likewise explicit capabilities, not global defaults.

## Syntax and semantics

`Ript/Syntax/` contains raw typed syntax, cost computation, and explicit
derivations. The raw syntax remains executable.

`Ript/Semantics/` contains:

- interpretations into costed categories;
- evaluation and cost soundness;
- equational soundness;
- quotient term models and relative completeness;
- symmetric monoidal semantics and initiality.

Quotients are confined to the proof layer. A consumer that only evaluates
finite syntax does not need to execute quotient machinery.

## Concrete models

`Ript/Models/` and its subdirectories implement semantic instances rather than
isolated data structures.

- `FiniteFunction` provides the deterministic baseline and explicit cartesian
  copy/discard behavior.
- `FiniteStochastic` provides normalized exact rational channels, composition,
  tensor, convex mixtures, copy, and discard.
- `FiniteDistribution` supplies the finite-distribution monad and Kleisli
  representation.
- probability modules bridge finite exact channels into Mathlib's `Stoch`.
- decision modules implement Blackwell comparison, exact risk, resource bounds,
  and separator certificates.
- computation modules distinguish formal step/query/storage/gate measures from
  wall-clock runtime.
- causal modules use finite topologically ordered DAGs and hard interventions.
- thermal modules separate exact operational channels from real-valued analytic
  thermodynamics.
- quantum modules use finite Kraus families, proving positivity and trace
  preservation before packaging channels.

The [model capability matrix](../MODEL_MATRIX.md) is the authoritative record
of which optional structures each model exports.

## Higher organization

`Ript/Higher/` packages complete process models into a bicategory:

- 0-cells are resource-indexed symmetric monoidal process models;
- 1-cells are resource-nonincreasing strong braided monoidal functors;
- 2-cells are monoidal natural transformations.

That fixed-resource bicategory is one fibre of a broader compiled layer.
`ResourceChangeModelHom` connects an `R`-model to an `S`-model over an ordered
additive map `R →+o S`; these heterogeneous 1-cells compose with their resource
maps, transport checked budgets, and have local categories of monoidal 2-cells
over each fixed resource map. `ResourceModel` packages each resource algebra
with its model, and `ResourceModelHom` packages the resource map with its
heterogeneous strong model morphism. `ResourceModelTransformation` retains
equality of parallel resource maps and a monoidal natural transformation.
Together they form a total bicategory with heterogeneous whiskering,
horizontal and vertical composition, interchange, associators, unitors,
pentagon, and triangle coherence.

The layer proves identities, composition, associators, unitors, interchange,
and coherence using Mathlib's bicategory infrastructure. Numerical cost
equality is not inferred from bicategorical equivalence; the stronger
`CostExactModelEquivalence` interface records reflection explicitly.

Localization work is split by strength:

- the model homotopy category has an ordinary Gabriel–Zisman localization;
- walking examples test genuine inverse-adjoining behavior;
- the exact bicategorical universal-property predicate is defined separately;
- unproved coherence or essential-surjectivity fields are never replaced by
  axioms.

## Internal univalent interpretation

`Ript/Univalent/` is downstream from the ordinary process theory. It defines:

- deep interface codes;
- separate internal structural-equivalence and identity syntax;
- a groupoid interpretation;
- 0-truncated object quotients and 1-truncated skeletons;
- representable presheaf and Yoneda semantics;
- simplicial nerves and a classifying diagram.

This is not external HoTT for Lean. In particular, Ript never postulates a
global map from `Equiv α β` to `α = β`. Claims are scoped to the internally
interpreted syntax and to the exact categorical interfaces compiled in the
project.

## Executable versus analytic boundaries

The finite core uses exact data where practical:

- natural-number resource vectors;
- finite types;
- nonnegative rational probabilities;
- decidable finite minima and explicit witnesses.

Real analysis, measure theory, quotient constructions, chosen representatives,
and matrix proofs live in semantic layers and may be noncomputable. A theorem
about finite objects is not automatically described as executable: the API and
its assumptions determine that classification.

## Public status records

Ript separates project communication from formal status:

- `README.md` is a concise entry point;
- `docs/RESEARCH_STATUS.md` gives a human-scale research summary;
- `MODEL_MATRIX.md` records compiled model capabilities;
- `BLUEPRINT.md` records dependencies and theorem-level status;
- `CONJECTURES.md` contains statements not yet proved;
- `AXIOMS.md` records actual kernel assumptions.

When these disagree, Lean declarations and machine-checked audit output take
precedence. Documentation changes should reconcile the human-facing files in
the same pull request.

## Quality architecture

`scripts/quality-gate.sh` is the stable local entry point and mirrors CI. It
enforces:

- no `sorry`, `admit`, project-specific axioms, trust escapes, or unsafe library
  declarations;
- narrow Mathlib imports and explicit identifiers;
- complete root-module coverage;
- warning-free full builds and declaration lint;
- stable executable examples;
- an explicit axiom allowlist;
- structurally valid public Markdown and bounded overview-page size.

The workflow uses pinned action revisions and read-only repository permissions.
See [CONTRIBUTING.md](../CONTRIBUTING.md) for the change policy.
