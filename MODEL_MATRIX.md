# Model Capability Matrix

Only implemented and compiled capabilities are marked as supported.

| Model | Sequential | Tensor | Discard | Copy | Convex | Causal | Decision | Thermal | Computable |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| FiniteFunction (zero cost) | Yes | Yes | Yes | Yes | No | Yes | No | No | Yes |
| FiniteFunction.Metered | Yes | No | No | No | No | No | No | No | Yes |
| Sequential term model | Yes | No | No | No | No | No | No | No | Proof layer |
| Symmetric monoidal term model | Yes | Yes | No | No | No | No | No | No | Proof layer |
| FiniteStochastic (exact `ℚ≥0`) | Yes | Yes | Yes | Yes | Yes | Yes | No | No | Yes |
| Finite-distribution Kleisli | Yes | No | No | No | No | No | No | No | Yes |
| Mathlib `Stoch` bridge (finite discrete image) | Yes | Yes | Via `Stoch` | Via `Stoch` | No | Via `Stoch` | Via Mathlib Bayes risk | No | Semantic layer |
| Exact finite decision layer | Via `FinStoch` | No | No | No | No | Via `FinStoch` | Yes | No | Yes |
| Total computation (`Fin 4 → Nat` resources) | Yes | Bifunctor | No | No | No | No | No | No | Yes |
| Partial computation (`Option` Kleisli) | Yes | Bifunctor | No | No | No | No | No | No | Yes |
| Finite causal DAG (exact `ℚ≥0`) | Topological generation | Via `FinStoch` states | No | No | No generic interface | Yes | No | No | Yes |
| Finite thermal systems (specified and realized Gibbs equilibrium) | Gibbs-preserving category | Bifunctor; realized Gibbs tensor at common temperature | No exported thermal discard | No | No generic interface | Via `FinStoch` | No | Yes: KL/free-energy and work-assisted Landauer bound | Exact states/channels executable; Gibbs/KL/free-energy/work accounting analytic layer |
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

The zero-cost finite-function row uses an explicit cartesian monoidal structure:
ordinary product types are tensor, `PUnit` is the unit, diagonal functions copy,
and the unique map to `PUnit` discards. Mathlib's `CopyDiscardCategory` supplies
the coherent commutative-comonoid laws, and every function is proved
deterministic and causal. The separate `Metered` row remains only sequential:
proof-relevant costs make morphisms with the same function but different units
distinct, so its category is not cartesian and no copy capability is inferred.

The finite-stochastic convex capability uses an explicit pair of nonnegative
`ℚ≥0` coefficients with a proof that their sum is exactly one. Pointwise
mixtures are normalized and satisfy endpoint, idempotence, branch-symmetry,
precomposition, postcomposition, and left/right tensor distribution laws. No
convex structure is inferred for another model unless that model exports its
own compiled instance.

The thermal row separates executable operational data from analytic
thermodynamics. `ThermalObject` stores an exact rational equilibrium and
`GibbsPreserving` stores exact stochastic channels. `FiniteGibbsData` constructs
real Boltzmann weights from energy and positive inverse temperature;
`GibbsThermalObject` explicitly certifies when those real probabilities agree
with the rational equilibrium. Every full-support exact equilibrium also has a
canonical realization at any positive inverse temperature. On this certified
intersection, Ript proves the finite KL/free-energy identity,
common-temperature monotonicity of excess Helmholtz free energy, and tensor
laws: weights/probabilities factor, partition functions multiply, and energy,
entropy, free energy, and free-energy gaps add on product states. It neither
assumes arbitrary independently specified exponential weights are rational nor
equates arbitrary battery free-energy loss with mechanical work. The
work-assisted layer proves that a Gibbs-preserving product-endpoint transition
must pay every system free-energy increase from battery free-energy decrease.
Only under an explicit entropy-neutral battery hypothesis does this become a
mean-energy work bound; the degenerate Boolean erasure instance costs at least
`log 2 / β`. Correlated endpoints, approximate erasure, and explicit bath or
cyclic-protocol models remain outside the current row.

The classical quantum row is the proved faithful measurement--preparation
image of `FiniteStochastic`. Its Kraus operators are
`sqrt(P(y | x)) |y><x|`, and its morphisms are invariant under source and
target dephasing. The target categorical identity is therefore dephasing,
which is why this row is listed separately from the full Kraus category.

## Resource-representation capabilities

These are generic representations over every implemented costed process model,
not extra semantic models, so they are recorded separately from the matrix.

| Representation | Serial law | Tensor law | Round trip | Choice | Computability |
| --- | --- | --- | --- | --- | --- |
| Cost-induced budget filtration | Identity at zero; layers compose at summed budgets | Available with `HasParallelProcessCost` | Least-budget reconstruction returns the original cost exactly | None introduced | Same as the source cost |
| Attained budget filtration | Reconstructed cost is subadditive | Available from explicit `TensorCompatible` evidence | Cost inequality is equivalent to original layer membership | None; least budget is explicit data | Same as the supplied `minimum` operation |

`AttainedHomFiltration` expresses exactly the hypothesis needed for the reverse
representation: every process has a least admissible budget and that budget is
itself admissible. Ript does not silently strengthen ordinary resource orders
to complete lattices. The executable `Metered`/`Nat` example reconstructs the
stored unit count and accepts double Boolean negation at budget `2` while
rejecting budget `1`.

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
| Object completion | Codes quotiented by mere internal identity | Equality is equivalent to inhabited internal identity/equivalence; sum/tensor coherence becomes literal equality | Quotient proof layer; executable maps descend from explicit invariants |
| Skeletal completion | Mathlib skeleton of the internal groupoid | Skeletal groupoid equivalent to the original; functor categories are equivalent; all automorphisms are retained | Noncomputable semantic layer using chosen representatives |
| Presheaf universe | Type-valued presheaves on the internal groupoid | Yoneda is fully faithful; representable transformations/isomorphisms correspond to internal identity/equivalence | Semantic proof layer; Mathlib Yoneda audits with classical choice |
| Yoneda envelope | Essential image of representables in the presheaf universe | Groupoid equivalent to the internal groupoid; inclusion factors Yoneda; functor categories are equivalent | Noncomputable essential-image witnesses; not a Rezk completion |
| Simplicial interface nerve | Ordinary categorical nerve of the internal groupoid | Complete Kan horn filling, strict Segal, quasicategory, 2-coskeletal; vertices/edges/2-simplices encode interfaces, identities, and composition; homotopy category recovers the groupoid | Semantic proof layer; chosen fillers audit with classical choice; no complete-Segal or Rezk claim |

The concrete Boolean model proves that `bit tensor unit` and `unit tensor bit`
are unequal syntax trees in Lean while tensor symmetry makes them internally
identical. Boolean negation transports across that identity and evaluates
exactly. The original internal-univalence layer and the object-completion
universal properties use no project axiom and no `Classical.choice`. The
separate skeletal categorical layer inherits `Classical.choice` from
Mathlib's chosen skeleton representatives and is marked noncomputable; it does
not feed data back into any executable model. Mathlib's nerve, strict Segal,
quasicategory, coskeletal, and homotopy-category infrastructure carries the
same classical audit footprint in the simplicial layer. Ript's ForMathlib
extension proves that every groupoid nerve is Kan and the chosen filler
interface has that same audited footprint.

Together these are a 0-truncated object completion and a 1-truncated skeletal
groupoid model, an ordinary representable-presheaf envelope, and the strict
categorical nerve of that groupoid. The nerve is a proved strict Segal
simplicial set, Kan complex, quasicategory, and 2-coskeletal object, but no
complete-Segal, Rezk-completion, or localization theorem is claimed. These layers do not add
`Equiv α β → α = β` and are not a Rezk completion or a complete presheaf model
of the full resource-process bicategory.
