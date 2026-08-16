# Model Capability Matrix

Only implemented and compiled capabilities are marked as supported.

| Model | Sequential | Tensor | Discard | Copy | Convex | Causal | Decision | Thermal | Computable |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| FiniteFunction (zero cost) | Yes | No | No | No | No | No | No | No | Yes |
| FiniteFunction.Metered | Yes | No | No | No | No | No | No | No | Yes |
| Sequential term model | Yes | No | No | No | No | No | No | No | Proof layer |
| Symmetric monoidal term model | Yes | Yes | No | No | No | No | No | No | Proof layer |
| FiniteStochastic (exact `ℚ≥0`) | Yes | Yes | Yes | Yes | No | Yes | No | No | Yes |
| Finite-distribution Kleisli | Yes | No | No | No | No | No | No | No | Yes |
| Mathlib `Stoch` bridge (finite discrete image) | Yes | Yes | Via `Stoch` | Via `Stoch` | No | Via `Stoch` | Via Mathlib Bayes risk | No | Semantic layer |
| Exact finite decision layer | Via `FinStoch` | No | No | No | No | Via `FinStoch` | Yes | No | Yes |
| Total computation (`Fin 4 → Nat` resources) | Yes | Bifunctor | No | No | No | No | No | No | Yes |
| Partial computation (`Option` Kleisli) | Yes | Bifunctor | No | No | No | No | No | No | Yes |
| Finite causal DAG (exact `ℚ≥0`) | Topological generation | Via `FinStoch` states | No | No | No generic interface | Yes | No | No | Yes |
| Finite thermal systems (specified equilibrium) | Gibbs-preserving category | Bifunctor | No exported thermal discard | No | No generic interface | Via `FinStoch` | No | Yes | Yes |
| Finite quantum Kraus channels (`ℂ`) | Kraus category | Yes | Yes | No | No | Yes | No | No | Matrix proof layer; basis labels executable |
| Classical quantum dephasing subcategory | Yes; identity is basis dephasing | Bifunctor | Via ambient trace discard, not separately packaged | No exported copy | No generic interface | Yes | No | No | Exact `FinStoch` source; noncomputable complex matrix semantics |

For the quantum row, “Discard” is the proved trace channel and “Causal” means
the compiled uniqueness/compatibility laws `eq_discard` and `comp_discard`.
Every channel's canonical complex-linear action is also proved completely
positive under identity amplification by every finite auxiliary system. This
is the ordinary finite-matrix formulation native to the current model, not an
unproved bridge to Mathlib's analytic C\*-algebra API. “Copy” remains
deliberately unsupported: no classical copying structure is inferred from the
chosen quantum basis.

The classical quantum row is the proved faithful measurement--preparation
image of `FiniteStochastic`. Its Kraus operators are
`sqrt(P(y | x)) |y><x|`, and its morphisms are invariant under source and
target dephasing. The target categorical identity is therefore dephasing,
which is why this row is listed separately from the full Kraus category.

## Higher categorical organization

The following table records structure relating complete process models. It is
kept separate from the per-model capability matrix because these are cells in
a bicategory, not additional operations inside any one semantic model.

| Dimension | Implemented carrier | Resource contract | Proved structure |
| --- | --- | --- | --- |
| 0-cells | Symmetric monoidal categories with serial, parallel, and free structural cost laws over one fixed resource type `R` | Every process cost is valued in the same ordered additive commutative monoid | `ProcessModel R` packages all required instances with uniform universes |
| 1-cells | Strong braided monoidal functors, represented as lax braided functors with invertible unit and tensor comparison maps | Mapping a process cannot increase its cost | Identities and composition; associator and left/right unitor isomorphisms |
| 2-cells | Monoidal natural transformations | No hidden numerical condition is inferred from naturality | Vertical and horizontal composition, identities, whiskering, and interchange |
| Coherence | Mathlib bicategory coherence specialized to model functors | Structural 2-cells do not silently alter the model-cost contract | Pentagon and triangle laws |
| Equivalence | Bicategorical equivalence plus explicit cost reflection in both directions | Forward and inverse functors preserve every process cost exactly | Budget preservation/reflection and transport of serial and parallel core bounds |

This layer is a bicategory of models for a fixed resource type and uniform
universes. It is not an `(∞,1)`-category, does not provide univalence, and does
not turn a Lean equivalence `Equiv α β` into an equality `α = β`. Ordinary
bicategorical equivalence alone also does not imply numerical cost equality:
`CostExactModelEquivalence` requires cost reflection explicitly.
