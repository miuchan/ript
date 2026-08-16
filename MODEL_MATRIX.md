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

## Internally univalent deep layer

This layer is downstream of the ordinary semantic models. It adds an
axiom-free internal identity interpretation without changing Lean's equality
or the executable cores.

| Component | Implemented representation | Proved contract | Computability |
| --- | --- | --- | --- |
| Interface universe | Deep codes generated by atoms, empty/unit, sum, and tensor | Codes have a small set-level interpretation | Raw syntax and interpretation are executable |
| Internal equivalence | Indexed structural-equivalence expressions, quotiented by interpreted equality | Reflexivity, inverse, composition, sum/tensor congruence | Raw expressions compute; quotient laws are proof layer |
| Internal identity | Separate path expressions with an internal `ua` constructor, quotiented by interpreted equality | Internal identity is equivalent to internal structural equivalence | Raw paths compute; quotient equality is proof layer |
| Groupoid model | Codes wrapped as objects; identities as morphisms | Category laws, inverses, and groupoid equations | Proof layer over computable interpretation |
| Deep processes | Typed generators, identity, serial composition, tensor, endpoint reindexing | Explicit derivations are sound in every generator interpretation | Evaluation is executable |
| Structure identity | Conjugation of deterministic function spaces along endpoint identities | Internally identical endpoints have equivalent process spaces | Executable on interpreted values |
| Indiscernibility | Predicates carrying explicit equivalence invariance | Internally identical/equivalent codes satisfy the same internal proposition | Proposition layer |

The concrete Boolean model proves that `bit tensor unit` and `unit tensor bit`
are unequal syntax trees in Lean while tensor symmetry makes them internally
identical. Boolean negation transports across that identity and evaluates
exactly. The audited layer uses no project axiom and no `Classical.choice`.

This is a small set-level, 1-truncated groupoid model. It is not an
`(∞,1)`-category, does not add `Equiv α β → α = β`, and is not yet a Rezk
completion or a presheaf model of the full resource-process bicategory.
