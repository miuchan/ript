# Model Capability Matrix

Only implemented and compiled capabilities are marked as supported.

<table>
  <thead>
    <tr>
      <th>Model</th>
      <th>Sequential</th>
      <th>Tensor</th>
      <th>Discard</th>
      <th>Copy</th>
      <th>Convex</th>
      <th>Causal</th>
      <th>Decision</th>
      <th>Thermal</th>
      <th>Computable</th>
    </tr>
  </thead>
  <tbody>
    <tr><td>FiniteFunction (zero cost)</td><td>Yes</td><td>Yes</td><td>Yes</td><td>Yes</td><td>No</td><td>Yes</td><td>No</td><td>No</td><td>Yes</td></tr>
    <tr><td>FiniteFunction.Metered</td><td>Yes</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>Yes</td></tr>
    <tr><td>Sequential term model</td><td>Yes</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>Proof layer</td></tr>
    <tr><td>Symmetric monoidal term model</td><td>Yes</td><td>Yes</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>Proof layer</td></tr>
    <tr><td>FiniteStochastic (exact <code>ℚ≥0</code>)</td><td>Yes</td><td>Yes</td><td>Yes</td><td>Yes</td><td>Yes</td><td>Yes</td><td>No</td><td>No</td><td>Yes</td></tr>
    <tr><td>Finite-distribution Kleisli</td><td>Yes</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>Yes</td></tr>
    <tr><td>Mathlib <code>Stoch</code> bridge (finite discrete image)</td><td>Yes</td><td>Yes</td><td>Via <code>Stoch</code></td><td>Via <code>Stoch</code></td><td>No</td><td>Via <code>Stoch</code></td><td>Via Mathlib Bayes risk</td><td>No</td><td>Semantic layer</td></tr>
    <tr><td>Exact finite decision layer</td><td>Via <code>FinStoch</code></td><td>No</td><td>No</td><td>No</td><td>No</td><td>Via <code>FinStoch</code></td><td>Yes: forward data processing, deterministic finite converse, and sound stochastic separation certificates; general stochastic converse formally stated but unproved</td><td>No</td><td>Exact finite minima, deterministic fiber witnesses, and genuinely stochastic <code>1/4 &lt; 1/2</code> separation certificate executable</td></tr>
    <tr><td>Total computation (<code>Fin 4 → Nat</code> resources)</td><td>Yes</td><td>Bifunctor</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>Yes</td></tr>
    <tr><td>Partial computation (<code>Option</code> Kleisli)</td><td>Yes</td><td>Bifunctor</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>No</td><td>Yes</td></tr>
    <tr><td>Finite causal DAG (exact <code>ℚ≥0</code>)</td><td>Topological generation</td><td>Via <code>FinStoch</code> states</td><td>No</td><td>No</td><td>No generic interface</td><td>Yes</td><td>No</td><td>No</td><td>Yes</td></tr>
    <tr><td>Finite thermal systems (specified and realized Gibbs equilibrium)</td><td>Gibbs-preserving category; finite closed and bath-assisted protocols</td><td>Bifunctor; realized Gibbs tensor at common temperature</td><td>No exported thermal discard</td><td>No</td><td>No generic interface</td><td>Via <code>FinStoch</code></td><td>No</td><td>Yes: exact rationality classification, irrational counterexample, closed-protocol no-go, KL/free-energy, correlation, bath-resolved and Landauer bounds</td><td>Exact states/channels/protocol traces/marginals, positive-rational weight normalization, information-battery, entropy-neutral work-battery, and closed erasure–recharge witnesses executable; arbitrary real exponential equality and Gibbs/KL/free-energy/work accounting remain analytic</td></tr>
    <tr><td>Finite quantum Kraus channels (<code>ℂ</code>)</td><td>Kraus category</td><td>Yes</td><td>Yes</td><td>No</td><td>No</td><td>Yes</td><td>No</td><td>No</td><td>Matrix proof layer; basis labels executable</td></tr>
    <tr><td>Classical quantum dephasing subcategory</td><td>Yes; identity is basis dephasing</td><td>Bifunctor</td><td>Via ambient trace discard, not separately packaged</td><td>No exported copy</td><td>No generic interface</td><td>Yes</td><td>No</td><td>No</td><td>Exact <code>FinStoch</code> source; noncomputable complex matrix semantics</td></tr>
  </tbody>
</table>

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
for arbitrary exact finite stochastic experiments and a complete converse for
deterministic experiments. With any full-support exact prior, a deterministic
source dominates a deterministic target exactly when its optimal zero-one
target-reconstruction risk is no larger than direct target observation;
equivalently, the target is constant on every source fiber. The executable
four-state example has risk `0` for an aligned partition and exactly `1/2` for
a crossing partition, ruling out every post-processing in the latter case.
The general stochastic Blackwell--Sherman--Stein converse remains unsupported.
Its exact Lean proposition now quantifies over every finite action carrier and
decision problem. A compiled reduction proves that proposition equivalent to
completeness of concrete decision-separation certificates, and every supplied
certificate is proved to rule out a garbling. The remaining unsupported step
is constructing such a rational certificate for every non-garbling pair.

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
