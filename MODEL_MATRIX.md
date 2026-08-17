# Model Capability Matrix

Only implemented and compiled capabilities are marked as supported.

The matrix is split into three keyed tables so it remains readable on narrow
screens and in Markdown clients that reject very wide tables. Rows have the
same order in every table.

## Process structure

| Model | Sequential | Tensor | Discard | Copy |
| --- | --- | --- | --- | --- |
| FiniteFunction (zero cost) | Yes | Yes | Yes | Yes |
| FiniteFunction.Metered | Yes | No | No | No |
| Sequential term model | Yes | No | No | No |
| Symmetric monoidal term model | Yes | Yes | No | No |
| FiniteStochastic (exact `ℚ≥0`) | Yes | Yes | Yes | Yes |
| Finite-distribution Kleisli | Yes | No | No | No |
| Mathlib `Stoch` bridge (finite discrete image) | Yes | Yes | Via `Stoch` | Via `Stoch` |
| Exact finite decision layer | Via `FinStoch` | No | No | No |
| Total computation (`Fin 4 → Nat` resources) | Yes | Bifunctor | No | No |
| Partial computation (`Option` Kleisli) | Yes | Bifunctor | No | No |
| Finite causal DAG (exact `ℚ≥0`) | Topological generation | Via `FinStoch` states | No | No |
| Finite thermal systems (specified and realized Gibbs equilibrium) | Gibbs-preserving category; finite closed and bath-assisted protocols | Bifunctor; realized Gibbs tensor at common temperature | No exported thermal discard | No |
| Finite quantum Kraus channels (`ℂ`) | Kraus category | Yes | Yes | No |
| Classical quantum dephasing subcategory | Yes; identity is basis dephasing | Bifunctor | Via ambient trace discard, not separately packaged | No exported copy |

## Semantic capabilities

| Model | Convex | Causal | Decision | Thermal |
| --- | --- | --- | --- | --- |
| FiniteFunction (zero cost) | No | Yes | No | No |
| FiniteFunction.Metered | No | No | No | No |
| Sequential term model | No | No | No | No |
| Symmetric monoidal term model | No | No | No | No |
| FiniteStochastic (exact `ℚ≥0`) | Yes | Yes | No | No |
| Finite-distribution Kleisli | No | No | No | No |
| Mathlib `Stoch` bridge (finite discrete image) | No | Via `Stoch` | Via Mathlib Bayes risk | No |
| Exact finite decision layer | No | Via `FinStoch` | Yes: forward data processing, deterministic and full finite stochastic Blackwell--Sherman--Stein converses, exact rational garbling-simplex representation, and rational-separator/decision-certificate equivalence | No |
| Total computation (`Fin 4 → Nat` resources) | No | No | No | No |
| Partial computation (`Option` Kleisli) | No | No | No | No |
| Finite causal DAG (exact `ℚ≥0`) | No generic interface | Yes | No | No |
| Finite thermal systems (specified and realized Gibbs equilibrium) | No generic interface | Via `FinStoch` | No | Yes: exact rationality classification, irrational counterexample, closed-protocol no-go, KL/free-energy, correlation, bath-resolved and Landauer bounds |
| Finite quantum Kraus channels (`ℂ`) | No | Yes | No | No |
| Classical quantum dephasing subcategory | No generic interface | Yes | No | No |

## Computability

| Model | Status |
| --- | --- |
| FiniteFunction (zero cost) | Yes |
| FiniteFunction.Metered | Yes |
| Sequential term model | Proof layer |
| Symmetric monoidal term model | Proof layer |
| FiniteStochastic (exact `ℚ≥0`) | Yes |
| Finite-distribution Kleisli | Yes |
| Mathlib `Stoch` bridge (finite discrete image) | Semantic layer |
| Exact finite decision layer | Exact finite minima, deterministic mixtures, rational convex-hull reflection, rational strict separation, fiber witnesses, the necessary empty-parameter boundary, and a genuinely stochastic `1/4 < 1/2` certificate are compiled |
| Total computation (`Fin 4 → Nat` resources) | Yes |
| Partial computation (`Option` Kleisli) | Yes |
| Finite causal DAG (exact `ℚ≥0`) | Yes |
| Finite thermal systems (specified and realized Gibbs equilibrium) | Exact states/channels/protocol traces/marginals, positive-rational weight normalization, information-battery, entropy-neutral work-battery, and closed erasure–recharge witnesses executable; arbitrary real exponential equality and Gibbs/KL/free-energy/work accounting remain analytic |
| Finite quantum Kraus channels (`ℂ`) | Matrix proof layer; basis labels executable |
| Classical quantum dephasing subcategory | Exact `FinStoch` source; noncomputable complex matrix semantics |

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

The exact finite decision layer proves both the forward Blackwell risk order
for arbitrary exact finite stochastic experiments and the full finite
Blackwell--Sherman--Stein converse on nonempty hidden-state carriers. It also
provides a direct deterministic proof: with any full-support exact prior, a deterministic
source dominates a deterministic target exactly when its optimal zero-one
target-reconstruction risk is no larger than direct target observation;
equivalently, the target is constant on every source fiber. The executable
four-state example has risk `0` for an aligned partition and exactly `1/2` for
a crossing partition, ruling out every post-processing in the latter case.
The stochastic theorem quantifies over every **nonempty** finite hidden
carrier, finite action carrier, and decision problem. The nonempty hypothesis
is forced by a compiled counterexample: for an empty hidden carrier the risk
order is vacuous, but no channel can garble a unit observation into an empty
one. Every stochastic garbling is represented exactly as a rational
simplex mixture of deterministic post-processings. A signed rational strict
separator exists exactly when a concrete decision-separation certificate
exists; row shifts and the uniform prior make the separator losses
nonnegative without changing comparisons. The geometric bridge is also proved:
a rational point in a finite real convex hull reflects to the rational convex
hull, real strict separation follows from Hahn--Banach, and density of rational
coefficient vectors preserves the finitely many strict inequalities. This gives
an exact rational separator, certificate completeness, and the full converse.

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
equates arbitrary battery free-energy loss with mechanical work. Instead, it
classifies the rationality boundary exactly: for any reference microstate, an
independently specified finite real spectrum has rational normalized Gibbs
probabilities iff every relative Boltzmann factor is a positive rational
number. Explicit positive rational weights construct executable exact
equilibria, including `(2, 1) -> (2/3, 1/3)` and
`(1, 2, 3) -> (1/6, 1/3, 1/2)`; a relative factor `sqrt 2` gives a proved
strict counterexample. Equality of arbitrary real exponential expressions is
not claimed decidable. The
work-assisted layer proves that a Gibbs-preserving product-endpoint transition
must pay every system free-energy increase from battery free-energy decrease.
Only under an explicit entropy-neutral battery hypothesis does this become a
mean-energy work bound; the degenerate Boolean erasure instance costs at least
`log 2 / β`. For arbitrary correlated endpoints, exact marginals are
executable; mutual information is proved equal to finite KL from the joint to
the product of its marginals and is nonnegative; joint free energy decomposes
into marginal gaps plus `I / β`; and the Landauer bound includes the exact
correlation free-energy change. For every exact rational error
`0 ≤ ε ≤ 1/2`, the executable approximate-erasure target has binary entropy,
cost `(log 2 - binEntropy ε) / β`, an antitone cost law, and product-endpoint
and correlation-corrected work bounds. `BathAssistedTransition` separately
accounts for system, bath, and battery free energy; exact bath return removes
the bath term, while an entropy-neutrality premise is required for the
mechanical-work form. The executable three-bit permutation witness exactly
erases a fair bit, returns a fair bath, consumes an erased information battery,
and saturates the free-energy balance at `log 2 / β`. Its proved battery
entropy change prevents it from being mislabeled as an entropy-neutral
work-bearing protocol. A second executable witness uses no bath: a genuinely
nondegenerate two-level battery with Gibbs weights `2/3` and `1/3` discharges
from its pure high state to its pure low state, keeps battery entropy exactly
zero, erases the fair memory exactly, and supplies precisely `log 2 / β` of
mean energy. Its certified Gibbs-preserving channel therefore attains the
mechanical Landauer work bound with equality. A matched
recharge channel is now executable as well: it randomizes the erased memory
back to equilibrium and uses the released `log 2 / β` of free energy to raise
the pure battery from low to high. Erasure followed by recharge has exact trace
`fair/high → erased/low → fair/high`; signed system and battery changes both
sum to zero, so the closed cycle is not a net-work source. The
row also includes executable finite closed same-system protocols, their
composite channel semantics, a nonconstant two-flip Boolean cycle, and the
theorem that no such closed protocol can erase the uniform equilibrium exactly.

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
| Homotopy 1-category | Model morphisms modulo invertible monoidal 2-cells | Raw cost reflection is multiplicative; its invertible-2-cell saturation is explicit | Bicategorical unitors/associator descend to strict ordinary category laws; saturated marking descends exactly to marked quotient classes |
| Cost-exact localization | Mathlib Gabriel--Zisman localization of the model homotopy category | Formally inverts every saturated cost-exact class | Genuine `Functor.IsLocalization`; canonical pseudofunctor from `Pith`; marked arrows map to isomorphisms; a noninvertible marked arrow and a noninvertible 2-cell expose nontriviality and truncation |
| Parameterized walking localization | Product of the locally discrete walking arrow with the one-object bicategory of types and functions | All first-coordinate arrows are marked when the retained coordinate is already an adjoint equivalence | Free-groupoid inversion in the first coordinate; endpoint-normal-form theorem, thinness, and an explicit equivalence with the codiscrete groupoid on `Fin 2`; faithful action on 2-cells; retained-, localized-, and separable mixed-coordinate lift families together with their full adjoint-equivalence closure; locally fully faithful precomposition, with modification naturality across the free inverse proved by mates; prospective strong-transformation lifts have reconstructed object components and a candidate constraint for every target 1-morphism, using source naturality forward and an explicit invertible mate in reverse; identity coherence, endpoint-normalized 2-cell naturality, inclusion-image composition coherence, and public-factor composition laws in both inverse/retained orders are proved by mate sliding; the mixed identity-retained specialization maps the formal inverse correctly while preserving noninvertible Boolean discard; both generator-cancellation orders, arbitrary nonseparable lifts outside that replete closure, and local essential surjectivity remain open |

This layer is a bicategory of models for a fixed resource type and uniform
universes. It is not an `(∞,1)`-category, does not provide univalence, and does
not turn a Lean equivalence `Equiv α β` into an equality `α = β`. Ordinary
bicategorical equivalence alone also does not imply numerical cost equality:
`CostExactModelEquivalence` requires cost reflection explicitly. The
localization is ordinary and noncomputable: the canonical higher bridge starts
from `Pith`, which retains only invertible 2-cells. A concrete finite
deterministic discard 2-cell has endpoints that remain distinct in the
homotopy category, proving why the bridge cannot extend to the full
bicategory with this locally discrete target. It is therefore not a
bicategorical, Dwyer--Kan, simplicial, or Rezk localization. The independent
parameterized walking construction is a non-locally-discrete test case: its
walking coordinate has no hidden path ambiguity, and its separable mixed
family is a genuine two-coordinate factorization result,
but it does not yet establish the universal lift for arbitrary nonseparable
pseudofunctors or the full local equivalence.

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
| Skeletal completion | Mathlib skeleton of the internal groupoid | Skeletal groupoid equivalent to the original; all automorphisms are retained; the completion functor is a Mathlib localization at every internal identity | Noncomputable semantic layer using chosen representatives |
| Presheaf universe | Type-valued presheaves on the internal groupoid | Yoneda is fully faithful; representable transformations/isomorphisms correspond to internal identity/equivalence | Semantic proof layer; Mathlib Yoneda audits with classical choice |
| Yoneda envelope | Essential image of representables in the presheaf universe | Groupoid equivalent to the internal groupoid; inclusion factors Yoneda; the restricted Yoneda functor is a Mathlib localization at all internal identities | Noncomputable essential-image witnesses; exact ordinary localization of an already-groupoidal source, not a Rezk completion |
| Simplicial interface nerve | Ordinary categorical nerve of the internal groupoid | Complete Kan horn filling, strict Segal, quasicategory, 2-coskeletal; vertices/edges/2-simplices encode interfaces, identities, and composition; homotopy category recovers the groupoid | Semantic proof layer; chosen fillers audit with classical choice; no complete-Segal or Rezk claim |
| Rezk classifying diagram | Outer simplicial category of composable interface strings, followed levelwise by the ordinary nerve | Every vertical level and horizontal row is a groupoid nerve and Kan; every horizontal row is strict Segal; the whole outer diagram is naturally `n ↦ Map(Δ[n], N(M.Object))`; `Map(∂Δ[n], N(M.Object))` is the genuine matching limit; every matching map is a fibration; the actual completeness map is presented as the nerve of a category equivalence | Semantic proof layer; exact project-local `GroupoidalCompleteSegal` witness proved; actual outer spine maps are equivalences in every bidegree; Mathlib-native weak-equivalence/standard complete-Segal packaging and localization of the full resource-process bicategory remain open |

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
The classifying-diagram layer preserves a second simplicial direction rather
than collapsing back to the strict nerve. Its outer `n`-object is the category
of `n`-strings and natural transformations; pointwise groupoid inversion makes
every vertical level Kan. The vertical-vertex row is naturally isomorphic to
the ordinary interface nerve, and vertical edges have explicit inverse and
cancellation laws. Flipping the two finite indexing categories naturally
identifies every horizontal row with an ordinary categorical nerve. The
resulting strict-Segal equivalence has the actual outer spine map as its
forward direction. Since every horizontal arrow is invertible, outer degree
one is the equivalence space; the actual outer zero-degeneracy is proved to be
the nerve of an explicit category equivalence. Independently, a strict
finite-ordinal universe bridge and Mathlib's closed-nerve comparison identify
the whole outer diagram naturally with `n ↦ Map(Δ[n], N(M.Object))`.
Presheaf density and closed internal Hom prove that
`Map(∂Δ[n], N(M.Object))` is the genuine categorical matching limit and that
boundary restriction is its universal lift. The pushout-product theorem then
proves that every matching map is a fibration.

Together these are a 0-truncated object completion and a 1-truncated skeletal
groupoid model, an ordinary representable-presheaf envelope, the strict
categorical nerve of that groupoid, and a levelwise controlled Rezk
classifying diagram with its categorical Rezk completeness comparison.
The natural matching presentation, matching-limit universal property, and
matching fibrations form a compiled project-local Reedy-fibrancy witness.
The identity, skeletal-completion, and restricted-Yoneda functors satisfy the
ordinary Mathlib localization universal property at all morphisms of the
already-groupoidal interface category. An exact project-local groupoidal
complete-Segal witness is also proved. A
Mathlib-native standard complete-Segal instance remains unavailable because
the pinned library has no simplicial weak-equivalence API; higher localization
that retains the full resource-process bicategory's 2-cell data also remains
open. Its ordinary homotopy 1-category localization is compiled separately.
These layers do not add `Equiv α β → α = β` and are not a complete presheaf
model or a proved higher localization of the full resource-process bicategory.
