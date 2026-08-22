# Model Capability Matrix

[English](MODEL_MATRIX.md) · [简体中文](../../zh-CN/reference/MODEL_MATRIX.md) ·
[日本語](../../ja/reference/MODEL_MATRIX.md) · [Esperanto](../../eo/reference/MODEL_MATRIX.md)

Machine-facing canonical record: [`../../../MODEL_MATRIX.md`](../../../MODEL_MATRIX.md).

Only implemented and compiled capabilities are marked as supported.

The matrix is split into three keyed native HTML tables so it remains readable
on narrow screens and renders in CommonMark clients that do not enable the GFM
table extension. Rows have the same order in every table.

## Process structure

<table data-ript-matrix="process-structure">
  <thead>
    <tr><th scope="col">Model</th><th scope="col">Sequential</th><th scope="col">Tensor</th><th scope="col">Discard</th><th scope="col">Copy</th></tr>
  </thead>
  <tbody>
    <tr><th scope="row">FiniteFunction (zero cost)</th><td>Yes</td><td>Yes</td><td>Yes</td><td>Yes</td></tr>
    <tr><th scope="row">FiniteFunction.Metered</th><td>Yes</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Sequential term model</th><td>Yes</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Symmetric monoidal term model</th><td>Yes</td><td>Yes</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">FiniteStochastic (exact <code>ℚ≥0</code>)</th><td>Yes</td><td>Yes</td><td>Yes</td><td>Yes</td></tr>
    <tr><th scope="row">Finite-distribution Kleisli</th><td>Yes</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Mathlib <code>Stoch</code> bridge (finite discrete image)</th><td>Yes</td><td>Yes</td><td>Via <code>Stoch</code></td><td>Via <code>Stoch</code></td></tr>
    <tr><th scope="row">Exact finite decision layer</th><td>Via <code>FinStoch</code></td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Total computation (<code>Fin 4 → Nat</code> resources)</th><td>Yes</td><td>Symmetric monoidal; exact resource addition</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Partial computation (<code>Option</code> Kleisli)</th><td>Yes</td><td>Bifunctor</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Finite causal DAG (exact <code>ℚ≥0</code>)</th><td>Topological generation</td><td>Via <code>FinStoch</code> states</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Finite thermal systems (specified and realized Gibbs equilibrium)</th><td>Gibbs-preserving category; finite closed and bath-assisted protocols</td><td>Symmetric monoidal product equilibria; realized Gibbs tensor at common temperature</td><td>No exported thermal discard</td><td>No</td></tr>
    <tr><th scope="row">Finite quantum Kraus channels (<code>ℂ</code>)</th><td>Kraus category</td><td>Full symmetric monoidal structure with reversible basis coherence</td><td>Yes</td><td>No</td></tr>
    <tr><th scope="row">Classical quantum dephasing subcategory</th><td>Yes; identity is basis dephasing</td><td>Faithful symmetric monoidal measurement--preparation image; full subcategory retains its tensor bifunctor</td><td>Via ambient trace discard, not separately packaged</td><td>No exported copy</td></tr>
  </tbody>
</table>

## Semantic capabilities

<table data-ript-matrix="semantic-capabilities">
  <thead>
    <tr><th scope="col">Model</th><th scope="col">Convex</th><th scope="col">Causal</th><th scope="col">Decision</th><th scope="col">Thermal</th></tr>
  </thead>
  <tbody>
    <tr><th scope="row">FiniteFunction (zero cost)</th><td>No</td><td>Yes</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">FiniteFunction.Metered</th><td>No</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Sequential term model</th><td>No</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Symmetric monoidal term model</th><td>No</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">FiniteStochastic (exact <code>ℚ≥0</code>)</th><td>Yes</td><td>Yes</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Finite-distribution Kleisli</th><td>No</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Mathlib <code>Stoch</code> bridge (finite discrete image)</th><td>No</td><td>Via <code>Stoch</code></td><td>Via Mathlib Bayes risk</td><td>No</td></tr>
    <tr><th scope="row">Exact finite decision layer</th><td>No</td><td>Via <code>FinStoch</code></td><td>Yes: forward data processing, deterministic and full finite stochastic Blackwell--Sherman--Stein converses, exact rational garbling-simplex representation, rational-separator/decision-certificate equivalence, universal semantic-order completeness, and exact all-task numeric-profile completeness for Blackwell equivalence</td><td>No</td></tr>
    <tr><th scope="row">Total computation (<code>Fin 4 → Nat</code> resources)</th><td>No</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Partial computation (<code>Option</code> Kleisli)</th><td>No</td><td>No</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Finite causal DAG (exact <code>ℚ≥0</code>)</th><td>No generic interface</td><td>Yes</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Finite thermal systems (specified and realized Gibbs equilibrium)</th><td>No generic interface</td><td>Via <code>FinStoch</code></td><td>No</td><td>Yes: exact rationality classification, irrational counterexample, closed-protocol no-go, KL/free-energy, correlation, bath-resolved and Landauer bounds</td></tr>
    <tr><th scope="row">Finite quantum Kraus channels (<code>ℂ</code>)</th><td>No</td><td>Yes</td><td>No</td><td>No</td></tr>
    <tr><th scope="row">Classical quantum dephasing subcategory</th><td>No generic interface</td><td>Yes</td><td>No</td><td>No</td></tr>
  </tbody>
</table>

## Computability

<table data-ript-matrix="computability">
  <thead>
    <tr><th scope="col">Model</th><th scope="col">Status</th></tr>
  </thead>
  <tbody>
    <tr><th scope="row">FiniteFunction (zero cost)</th><td>Yes</td></tr>
    <tr><th scope="row">FiniteFunction.Metered</th><td>Yes</td></tr>
    <tr><th scope="row">Sequential term model</th><td>Proof layer</td></tr>
    <tr><th scope="row">Symmetric monoidal term model</th><td>Proof layer</td></tr>
    <tr><th scope="row">FiniteStochastic (exact <code>ℚ≥0</code>)</th><td>Yes</td></tr>
    <tr><th scope="row">Finite-distribution Kleisli</th><td>Yes</td></tr>
    <tr><th scope="row">Mathlib <code>Stoch</code> bridge (finite discrete image)</th><td>Semantic layer</td></tr>
    <tr><th scope="row">Exact finite decision layer</th><td>Exact finite minima, deterministic mixtures, rational convex-hull reflection, rational strict separation, fiber witnesses, the necessary empty-parameter boundary, and a genuinely stochastic <code>1/4 &lt; 1/2</code> certificate are compiled</td></tr>
    <tr><th scope="row">Total computation (<code>Fin 4 → Nat</code> resources)</th><td>Yes</td></tr>
    <tr><th scope="row">Partial computation (<code>Option</code> Kleisli)</th><td>Yes</td></tr>
    <tr><th scope="row">Finite causal DAG (exact <code>ℚ≥0</code>)</th><td>Yes; fixed-DAG soft/stochastic/hard programs have computable last-write-wins and redundant-mechanism reduction</td></tr>
    <tr><th scope="row">Finite thermal systems (specified and realized Gibbs equilibrium)</th><td>Exact states/channels/protocol traces/marginals, positive-rational weight normalization, information-battery, entropy-neutral work-battery, and closed erasure–recharge witnesses executable; arbitrary real exponential equality and Gibbs/KL/free-energy/work accounting remain analytic</td></tr>
    <tr><th scope="row">Finite quantum Kraus channels (<code>ℂ</code>)</th><td>Matrix proof layer; basis labels, finite instrument outcomes, and branch enumeration executable</td></tr>
    <tr><th scope="row">Classical quantum dephasing subcategory</th><td>Exact <code>FinStoch</code> source; noncomputable complex matrix semantics</td></tr>
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

The full Kraus tensor, associator, unitors, and swap form a compiled symmetric
monoidal category. Naturality against arbitrary Kraus channels and the
pentagon, triangle, both hexagons, and symmetry are proved on the full category,
not only on the classical dephasing image.

The finite quantum instrument layer separates completely positive operation
branches from their trace-preserving sum. Outcome probabilities are
nonnegative `NNReal` values normalized to one; positive outcomes have posterior
density matrices; serial composition records paired outcomes; independent
tensor products multiply outcome probabilities. Every instrument is represented
by a CPTP channel into `Outcome × residual-system`, with an exact theorem that
recovers each branch from its diagonal classical block and proves off-diagonal
blocks vanish. The coherent plus-state example has two exact half-probability
measurement outcomes and exact quarter-probability pairs. Outcome-controlled
Pauli-X feedback preserves those weights while sending both posteriors and the
forgotten-result total to the `false` basis state. `InstrumentSyntax` adds both
the one-unit recorded measurement and two-unit adaptive correction to the
resource-aware symmetric monoidal syntax and its canonical free lift.
Dependent bind allows the continuation and its finite result type to depend on
the preceding outcome; joint probabilities obey Born's chain rule and nested
binds associate after canonical Sigma-type relabeling. The compiled two-round
tree has three histories with probabilities `1/2`, `1/2`, and `0`, and its
two-unit recorded channel is another free-syntax generator. `InstrumentTree`
is the corresponding first-class inductive syntax: its dependent history type
is a canonical normal form, evaluation has an exact history-branch
representation theorem, and every exact history cost is bounded by a
computable structural tree budget. The classical-record channel is injective
on finite instruments; after an explicit equivalence of dependent histories,
recorded-channel equality, evaluated-instrument equality, and equality of all
recursive branch maps are equivalent. An arbitrary channel with output
`Outcome × residual-system` is in this recorded image exactly when its
outcome blocks are diagonal; Kraus-row slicing constructs the unique
instrument, and a one-step tree realizes it up to canonical history relabeling.

The randomized-computation model pairs an executable exact `FinStoch` kernel
with `ComputationResource`. Composition and tensor add steps, queries, storage,
and gates exactly; all symmetric monoidal coherence programs have zero cost;
componentwise budget checking is executable and sound. Forgetting the resource
recovers probability behavior, but equality and budgets retain the computation
data.

## Six-model exact noise slice

`NoisyBitRealizations` interprets one literal unit-cost BSC generator with
stay probability `3/4` and crossover probability `1/4`:

| Model | Realization and checked evidence |
| --- | --- |
| Probability | Exact rational BSC entries |
| Quantum | Random-unitary identity/Pauli-X mixture; fixes the coherent plus state and differs from measurement--preparation off diagonal |
| Causal | Exact noisy child mechanism conditioned on its parent |
| Computation | Exact randomized program; one step/query/gate, with exact doubled parallel resource |
| Semantic information | Boolean guessing risk `1/4` and value `1/4` relative to no information |
| Thermodynamics | Symmetric BSC preserves the uniform Gibbs equilibrium |

`sixModelNoiseAgreement` packages the common boundary and
`sixModelNoiseFreeLiftOnGenerator` packages the six canonical strong symmetric
resource-changing free lifts.

## Six-model adaptive branching-tree slice

`Ript.Syntax.Branching` provides an executable fixed-depth binary tree
language whose next generator may depend on the outcome already observed.
Complete histories carry exact positive rational weights, deterministic state
updates, exact path costs, and a worst-case budget.  The canonical normal form
is a finite history table.  Its recorded `FinStoch` representation is faithful,
so `observationalCompleteness` proves equality of recorded channels exactly
when the canonical tables agree.

`AdaptiveNoiseRealizations` instantiates the language with quarter-flip and
half-flip generators.  The second generator is selected by the first outcome;
the four histories have masses `9/16`, `3/16`, `1/8`, and `1/8`, and the
worst-case common cost is `3`.

| Model | Native adaptive-tree realization and checked evidence |
| --- | --- |
| Probability | Exact history-recording channel and finite-table representation/completeness |
| Quantum | Random-unitary `InstrumentTree`; every classical-basis diagonal block equals the common table, while a coherent off-diagonal block distinguishes it from measurement--preparation |
| Causal | Four-node DAG; the observational joint factors exactly as fair input times the protocol conditional |
| Computation | Exact randomized program with resource vector `(steps, queries, storage, gates) = (3, 3, 2, 3)` |
| Semantic information | Complete-history decoding is a deterministic retraction; Bayes risk is `0` and guessing value is `1/2` |
| Thermodynamics | The channel is Gibbs-preserving for its induced output equilibrium; every history/output mass is the branch mass divided by two |

`sixModelAdaptiveRepresentation` packages these boundaries.
`adaptiveProtocol_run_ne_fixedQuarter` uses observational completeness to
separate the adaptive protocol from a fixed two-quarter-flip tree.

## Variable-depth dependent finite branching

`DependentBranching` generalizes the common stochastic layer so every
generator owns an arbitrary finite outcome type and every result selects an
arbitrary continuation. Dependent Sigma histories, enumeration, equality,
length, height, exact path cost, and finite-supremum worst-case budget are
computable. Positive rational semantics has a canonical recorded table;
comparison across different history types requires an explicit equivalence,
and `observationalCompletenessAlong` proves behavior equality exactly when the
reindexed tables agree. `BinaryEmbedding` preserves probability, state, cost,
and stochastic entries from the fixed-depth binary theory.

The executable heterogeneous witness combines `Bool` and `Fin 3` results,
producing five histories of lengths one through three, height `3`, budget `4`,
and exact masses `1/2, 1/6, 1/6, 1/12, 1/12`. This discharges the generic
variable-depth/arbitrary-finite-outcome stochastic representation boundary.
`DependentBranching.Free` now supplies the category of branching algebras, an
initial tree algebra, unique fold interpretation, an absolutely complete
equational congruence, and associative unital sequential leaf grafting. Height
and budget are canonical folds and are subadditive under grafting; the example
computes leaf count `5`, doubled height `6`, and doubled budget `8`. Parallel
symmetric-monoidal structure now exists on the category of model algebras:
product fold is the exact pair of model interpretations, and the term-model
product is jointly complete. `ParallelProtocol` now adds binary tree-level
independent lanes with paired histories/states, exact stochastic factorization,
lane symmetry, additive resources, and strict tensor–graft interchange. The
fair/biased witness has `25` histories, budget `8`, short mass `3/8`, and
two-phase budget `16`. This is generalized by `LaneProtocol`: lane-indexed signatures,
states, histories, and semantics may all depend on an arbitrary finite lane
type; probabilities normalize as a finite product, channel entries factor
n-arily, and lane equivalences preserve probability, budget, and the whole
canonical normal form under explicit dependent history/state transport; strict
n-ary interchange holds. The three-lane witness has `125` histories, budget
`12`, short mass `3/16`, a checked two-lane transposition, and two-phase budget
`24`.

`DependentBranchingRealization` now maps every canonical finite positive
dependent normal form into all six model families. The common channel is
realized directly in probability, faithfully by measurement–preparation in
quantum theory, as valid entries of a tagged two-node causal joint, as a
four-resource randomized program, as a full experiment in a fixed semantic
task context, and as a Gibbs-preserving map into the induced output
equilibrium. Each model reflects normal-form equality at its stated boundary;
causal reflection requires a full-support prior. The generic resource map
bounds every path cost by steps/gates and every history length by
queries/storage. Separately, arbitrary finite hard-intervention programs have
a computable last-write-wins normal form, exact one-intervention stochastic
representation, and equality-reflection completeness whenever the base local
mechanisms are not already forced Dirac constants. The fixed-DAG generalization
now permits arbitrary parent-dependent soft replacements, parent-independent
stochastic interventions, and embedded hard interventions. Its computable
normal form performs last-write-wins reduction and erases explicit writes of
the base mechanism; reduced local semantics is injective, program execution is
one normalized intervention, and the normalized program channel is exact.
Heterogeneous-carrier, graph-changing, or policy-dependent causal
interventions, resource-bounded or richer/infinite-task semantic-profile
completeness, and energy-resolved thermal-operation dilation images remain
open; the coherent finite quantum instrument-tree image and its operational
equality reflection are compiled. At the Gibbs-preserving thermal
boundary, an arbitrary externally specified target equilibrium admits a unique
lift of a channel exactly when it equals the source-equilibrium pushforward;
compatible normal-form lifts reflect equality. At the exact unbounded
finite-task boundary,
universal nonnegative semantic value is equivalent to Blackwell dominance, and
equality of the entire no-information-relative numeric value profile is
equivalent to Blackwell equivalence. A Boolean witness proves that one scalar
task value alone is not complete.


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

## Common six-model syntax slice

The unit-cost sequential signature in
`Ript.Examples.CommonBitRealizations` is one literal syntax interpreted in
all six model families. It preserves the native computation resource and makes
the other current abstract-cost contracts and model-specific proof obligations
explicit.

| Model family | Concrete realization | Native resource interpretation | Checked observable |
| --- | --- | --- | --- |
| Classical probability | Exact deterministic `FinStoch` negation | Scalar `Nat`, zero channel cost bounded by one | Negated output has probability one |
| Quantum process | Pauli-X Kraus channel | Scalar `Nat`, zero abstract channel cost bounded by one | Basis density `|b><b|` maps to `|¬b><¬b|` |
| Causal model | Negating child mechanism in the finite two-node DAG | Scalar `Nat`, zero stochastic cost bounded by one | Child is the negation of its parent with probability one |
| Computation | Total Boolean gate | `ComputationResource`; one scalar unit maps to one step and one gate | Executed result is Boolean negation and translated cost is exact |
| Semantic information | Reversibly relabeled Boolean experiment | Scalar `Nat`, zero channel cost bounded by one | Blackwell-equivalent to perfect observation; guessing value is exactly `1/2` |
| Thermodynamics | Gibbs-preserving flip of the degenerate thermal bit | Scalar `Nat`, zero abstract process cost bounded by one | Exact channel flips the bit and preserves equilibrium |

`sixModelFlipAgreement` packages these six facts into one kernel-checked
proposition. It is a nontrivial shared slice, not yet a representation or
completeness theorem for the full six model families.

`Ript.Examples.CompositionalBitRealizations` extends this boundary to two
typed stages. Its checked composite uses the native composition mechanism of
each model:

| Model | Two-stage evidence |
| --- | --- |
| Probability | Chapman--Kolmogorov composition of two exact negations is identity |
| Quantum | Two Pauli-X applications restore every computational-basis density matrix |
| Causal | A normalized three-node DAG contains two negating child mechanisms; their common boundary composite is identity |
| Computation | Two gates restore the input and store exactly two steps plus two gates |
| Semantic information | Reversible post-processing recovers perfect observation and exact value `1/2` |
| Thermodynamics | The two free flips denote the identity closed Gibbs-preserving protocol |

These facts are packaged by `sixModelCompositionAgreement`. The shared syntax
proves serial compositional agreement. The separate adaptive-tree slice above
now covers fixed-depth binary branching with two exact noise generators;
general measurement instruments and a free variable-depth branching theory
remain outside this reversible slice.

The linear compositional theory now also has exact representation and
completeness results. `normalize` computes the unique canonical path for every
well-typed expression; `derives_unique` proves all fixed-endpoint expressions
formally equal; `inImage_iff_eq_canonical` identifies each interpretation's
hom-image as the singleton containing that path; and
`sixModelSemanticCompleteness` proves equality reflection for all six models.
This strength relies on the current linear graph being thin and is not claimed
for the richer operational language below.

`Ript.Examples.OperationalErasureRealizations` adds the first characteristic
irreversible operation. The common resource algebra records exposure and
erasure separately. Its computation map sends them exactly to one query and
one gate, while the thermal interpretation enlarges the interface to memory
plus work battery instead of claiming free erasure.

| Model | Operational erasure evidence |
| --- | --- |
| Probability | Perfect exposure followed by deterministic constant-false erasure |
| Quantum | Measurement--preparation reset sends every diagonal basis state to pure `false` |
| Causal | The child channel is erased and `do(effect=false)` is proved to replace its local mechanism |
| Computation | Constant program returns `false` with exact cost: two steps, one query, one gate |
| Semantic information | Post-processing becomes Blackwell-equivalent to the uninformative baseline and exact value drops from `1/2` to zero |
| Thermodynamics | Joint memory--battery Gibbs-preserving erasure consumes the pure high battery and saturates the entropy-neutral Landauer work equality |

`sixModelErasureAgreement` packages these facts. Quantum and thermal analytic
claims remain proof-layer statements; the finite operational boundaries remain
explicit and machine checked.

## Six-model parallel syntax slice

`ParallelBitRealizations` supplies the first literal common symmetric
monoidal language. Its expression `flip ⊗ flip` has exact syntax cost `2` and
is interpreted in all six model families. Its quantum target is the full finite
Kraus category rather than only the measurement--preparation image:

| Model | Checked parallel evidence |
| --- | --- |
| Probability | Product stochastic channel negates both Boolean components with probability one |
| Quantum | Tensor Pauli-X acts componentwise on arbitrary product density matrices and maps each two-bit basis density to the doubly negated state |
| Causal | Two independent copies of the finite-DAG child mechanism negate their respective parent assignments |
| Computation | Product execution returns both negations and adds the exact four-coordinate resources |
| Semantic information | Independent experiment post-processing relabels both observations reversibly |
| Thermodynamics | Tensor of two Gibbs-preserving flips negates both states and preserves the product equilibrium |

Monoidal cost translation is now proof-theoretically conservative, and every
heterogeneous monoidal interpretation has a direct strong symmetric
`ResourceChangeFunctor` from the original free term model. The strict
extension type is contractible. `sixModelMonoidalFreeLiftOnGenerator`
instantiates this universal property for all six parallel interpretations.
`ParallelBitHigherModels` then packages the common free syntax and the six
targets, including the full Kraus process model, as objects of the total
resource-model bicategory. The six free lifts
become strong braided one-cells with checked resource maps; the computation
one-cell retains the exact four-coordinate parallel cost.

## Non-thin diamond representation and completeness

The reusable foundation is now generic. `SequentialNormalForm` represents
expressions of any typed sequential signature by generator paths, proves
derivability iff path equality, gives a computable hom-set equivalence between
the quotient term model and typed paths, upgrades it to an explicit category
equivalence with exact free-cost preservation, identifies every heterogeneous
interpretation's semantic image with its path image, and proves every
path-faithful interpretation complete. `SequentialFree` proves the unique
resource-nonincreasing extension of every ordinary interpretation, while
`ResourceChangingSequentialFree` proves the corresponding unique extension
along an explicit `φ : R →+o S`; in both cases the complete type of strict
extensions is contractible. Globally, ordinary interpretations are equivalent
to free-source `ResourceMonotoneFunctor`s, and heterogeneous interpretations
are equivalent to free-source `ResourceChangeFunctor`s with the advertised
resource map. None of these results assumes finiteness, acyclicity, or thinness.

`DiamondBitTheory` combines the reversible and erasure branches into one free
category with two parallel input-to-output paths. Their independent resource
coordinates prove they are not formally derivable as equal. Normalization
retains both paths and yields:

- an exact ten-path canonical representation;
- an exact two-element input-to-output semantic image;
- a completeness criterion saying path separation implies equality reflection.

`DiamondBitRealizations` verifies path separation in all six models using
model-specific evidence. Hence all six interpretations are complete for this
non-thin theory. This is the first completeness result in Ript where the model
must distinguish competing syntax paths rather than inheriting completeness
from a thin source. The same six interpretations now also induce canonical
resource-changing functors from one free diamond term model; generator
agreement and translated cost bounds hold for every free morphism.

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
| 0-cells in one fibre | Symmetric monoidal categories with serial, parallel, and free structural cost laws over one resource type `R` | Every process cost in that fibre is valued in the same ordered additive commutative monoid | `ProcessModel R` packages all required instances with uniform universes |
| 0-cells across fibres | `ResourceModel` bundles a resource type, its ordered additive structure, and one `ProcessModel` | Each object retains its own resource algebra | All bundles share uniform universes and form the objects of one total bicategory |
| Resource base change | Ordered additive homomorphisms `φ : R →+o S` | Serial, parallel, structural, and checked budget laws are transported by applying `φ` | Cost reindexing, model reindexing, identities, composition, and executable `Fin 4 → Nat` step projection |
| Common sequential syntax | One sequential signature interpreted in an arbitrary costed category, optionally along `φ : R →+o S` | The canonical free lift is resource-nonincreasing, or bounded by `φ` of the exact source cost; the path equivalence preserves free cost exactly | Interpretation/free-source-functor classification equivalence; contractible strict-extension type; term-category/path-category equivalence; exact path-image representation; path-faithful completeness |
| Common syntax base change | One monoidal signature with costs in `R`, interpreted in an `S`-costed symmetric monoidal model along `φ : R →+o S` | Wires and generators are unchanged; every expression budget becomes exactly `φ` of its original computed budget | Computably invertible expression and derivation translation; proof-theoretic conservativity; direct strong symmetric resource-changing free lift; contractible strict extension type; translated free-model completeness |
| Heterogeneous 1-cells | `ResourceModelHom` pairs `φ : R →+o S` with a strong braided monoidal functor from an `R`-model to an `S`-model | Target cost is at most `φ` of source cost | Identity, composition over `ψ.comp φ`, canonical reindexing maps, transported budget certificates, and an executable vector-to-step model map |
| Heterogeneous 2-cells | Monoidal natural transformations between 1-cells with propositionally equal resource maps | No hidden numerical condition is inferred from naturality | Vertical and horizontal composition, identities, left/right whiskering, interchange, and total local categories |
| 1-cells in one fibre | Strong braided monoidal functors, represented as lax braided functors with invertible unit and tensor comparison maps | Mapping a process cannot increase its cost | Identities and composition; associator and left/right unitor isomorphisms |
| 2-cells in one fibre | Monoidal natural transformations | No hidden numerical condition is inferred from naturality | Vertical and horizontal composition, identities, whiskering, and interchange |
| Coherence | Mathlib bicategory coherence specialized both to fixed-resource and total resource-model functors | Structural 2-cells do not silently alter the model-cost contract | Associators, unitors, pentagon, and triangle laws in both bicategories |
| Total-model object core | Nerve of the core of the bicategorical homotopy category | Chosen bicategorical equivalences are quotiented only when they induce the same object-nerve edge | Kan, strict Segal, 2-coskeletal; internal equivalence classes are exactly object-identity edges and every edge has a bicategorical-equivalence representative |
| Total-model local mapping nerves and global Duskin nerves | Ordinary nerve of every full local hom-category; an all-dimensional coordinate semi-simplicial nerve; and a native full nerve whose `n`-simplices are strictly unitary lax functors `[n] → ResourceModel` | Vertices retain resource-changing 1-cells; edges retain all monoidal 2-cells; triangles retain arbitrary composite comparisons; lax associativity is exactly the associator-corrected tetrahedral equation | Local nerves are strict Segal, quasicategorical, and 2-coskeletal; every monotone ordinal map acts by normal-lax precomposition; all faces and degeneracies satisfy strict functor laws; native simplices decode naturally to coordinates; a constructor-normal ordinal equivalent to `Fin (n+1)` now computes identity/strict edges and unitor/strict comparison cells, with the all-strict tetrahedral branch proved |
| Equivalence | Bicategorical equivalence plus explicit cost reflection in both directions | Forward and inverse functors preserve every process cost exactly | Budget preservation/reflection and transport of serial and parallel core bounds |
| Homotopy 1-category | Model morphisms modulo invertible monoidal 2-cells | Raw cost reflection is multiplicative; its invertible-2-cell saturation is explicit | Bicategorical unitors/associator descend to strict ordinary category laws; saturated marking descends exactly to marked quotient classes |
| Cost-exact localization | Mathlib Gabriel--Zisman localization of the model homotopy category | Formally inverts every saturated cost-exact class | Genuine `Functor.IsLocalization`; canonical pseudofunctor from `Pith`; marked arrows map to isomorphisms; a noninvertible marked arrow and a noninvertible 2-cell expose nontriviality and truncation |
| Parameterized walking localization | Product of the locally discrete walking arrow with the one-object bicategory of types and functions | All first-coordinate arrows are marked when the retained coordinate is already an adjoint equivalence | Free-groupoid inversion in the first coordinate; endpoint-normal-form theorem, thinness, and an explicit equivalence with the codiscrete groupoid on `Fin 2`; faithful action on 2-cells; every source strong transformation and modification lifts, and precomposition is an equivalence on every local category; every arbitrary marking-inverting source pseudofunctor extends to `generalLiftPseudofunctor`; all sixteen endpoint associativity sequences compile in arbitrary destination bicategories; `generalLiftFactorization` gives the source-restriction adjoint equivalence, `generalLiftFactorsThrough` gives arbitrary nonseparable biessential factorization, and `inclusion_isBicategoricalLocalization` packages the complete bicategorical universal property |

Each fixed-resource fibre is a bicategory of models with uniform universes.
The heterogeneous layer now packages those fibres into a total bicategory,
including horizontal 2-cell composition and coherence across resource
changes. Its new two-level simplicial bridge supplies a Kan object-equivalence
core with an exact internal-equivalence/edge correspondence and full local
mapping nerves that retain noninvertible 2-cells. A native full Duskin nerve
now packages strictly unitary lax finite-ordinal diagrams with every face and
degeneracy, and decodes naturally to the coordinate semi-simplicial nerve.
The degreewise coordinate equivalence and complete Segal 2-space assembly are
not yet proved, and this construction does not turn a Lean equivalence
`Equiv α β` into an equality `α = β`. Ordinary
bicategorical equivalence alone also does not imply numerical cost equality:
`CostExactModelEquivalence` requires cost reflection explicitly. The
localization is ordinary and noncomputable: its canonical bridge starts from
`Pith`, which retains only invertible 2-cells. The separate local mapping nerve
does retain the concrete noninvertible deterministic discard 2-cell and proves
that it stays noninvertible after total-model packaging. Thus the ordinary
localization is still not bicategorical, Dwyer--Kan, simplicial, or Rezk; the
new simplicial bridge is a representation layer, not yet a localization. The independent
parameterized walking construction is a non-locally-discrete test case: its
walking coordinate has no hidden path ambiguity, and its separable mixed
family is a genuine two-coordinate factorization result. Its local
precomposition functors are equivalences, and the arbitrary source action is
already functorial on every hom-category, but the identity/composition
comparison and coherence needed for the universal nonseparable lift are not
yet established.

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
| Rezk classifying diagram | Outer simplicial category of composable interface strings, followed levelwise by the ordinary nerve | Every vertical level and horizontal row is a groupoid nerve and Kan; every horizontal row is strict Segal; the whole outer diagram is naturally `n ↦ Map(Δ[n], N(M.Object))`; `Map(∂Δ[n], N(M.Object))` is the genuine matching limit; every matching map is a fibration; the actual completeness map has an explicit simplicial homotopy inverse | Semantic proof layer; exact project-local `GroupoidalCompleteSegal` and `HomotopyEquivalenceWitness` evidence proved; the full cost-exact localization, common-universe local comparison, localization-aware all-dimensional relative outer Rezk map, source/target completeness witnesses, arbitrary-2-cell one-skeleton glue, vertical local 2-simplex/composite-diagonal glue, degree-one horizontal compositor squares, degree-two vertical pasting/interchange, the explicit three-tetrahedron degree-two compositor prism, all-degree local prism coherence, arbitrary outer-string vertex/restriction comparison, relative-outer gluing of every all-degree prism source vertex, strict decoded-pair naturality for every restriction, exact side-sensitive outer/local glue for every actual target prism-face vertex, a categorical-nerve equivalence from the presented relative-zigzag mapping nerve to every actual target local nerve, strict all-degree local-map factorization, outer essential surjectivity, target-independent algebraic/simplicial presentation universality, an audited `PresentedDwyerKanCore`, an independent right-associated linear hammock mapping category equivalent to the binary presentation and actual target local nerve, an audited `LinearHammockDwyerKanCore`, an exact arbitrary-height row-grid representation of every linear-hammock simplex, exact quotient/nerve interpretation of the fixed-shape aligned multi-column fragment, an executable elementary forward/marked-pair refinement calculus, an object-level common-refinement quotient sound for semantic isomorphism, a zero-truncated thin refinement-groupoid nerve equivalent to the discrete quotient nerve, a non-thin semantic refinement-path groupoid nerve with exact edge action, its categorical/nerve equivalence to the exact refinement-generated quotient-cell image subgroupoid, and a faithful aligned-cell-augmented non-groupoidal path category containing every source 2-cell in canonical one-column form with strict refinement-nerve factorization are proved; normalization of every presented quotient 2-cell into the generated hammock paths, competing-move coherence, reduced-hammock invariance, standard weak-equivalence packaging, and the final Dwyer--Kan comparison remain open |

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
complete-Segal witness is also proved. Its completeness map now carries an
explicit simplicial inverse and genuine homotopies for both inverse laws. A
Mathlib-native standard complete-Segal instance remains unavailable because
the pinned library has no simplicial weak-equivalence API. The full
resource-process bicategory's cost-exact higher localization is now proved by
the executable marked-zigzag presentation, retaining its 2-cell data and
satisfying marked inversion, biessential factorization, and local equivalence.
Its common-universe full-local-nerve and actual-target outer Rezk comparisons
are also compiled, with exact vertex, identity, composition, vertical
two-simplex, arbitrary-horizontal-2-cell compositor-square gluing, and
degree-two vertical pasting/interchange. The actual degree-two compositor
prism is now represented by three target-local 3-simplices with all twelve
faces identified. Arbitrary-degree target prism simplices and all seven
endpoint/side/shared/degeneracy law families are now packaged globally for
every model triple. Relative outer degree-two two-arrow vertices now have exact
three-face/two-degeneracy laws; relative comparison preserves them, and all
three horizontal pair vertices of each local prism glue to their target outer
faces. Arbitrary outer string vertices, every simplex restriction, and their
relative comparison are now exact; every source vertex of every all-degree
local prism decodes to a fully glued relative two-arrow vertex. This decoding
is strictly natural under every simplex restriction, and complete glue is
proved again at every restricted source vertex, covering all faces and
degeneracies uniformly. Every actual target-prism face vertex is now projected
literally, classified on the two sides of the compositor switch, identified
with its exact local presentation, and decoded to the same outer composite.
The full local face core remains attached, so noninvertible local cells are
not collapsed into outer equalities. The relative-zigzag mapping-space
presentation is now explicit: for every model pair its word/quotient-2-cell
nerve is categorically equivalent to the actual target local nerve, has an
explicit simplicial homotopy inverse, and strictly factors the existing local
map in every degree. The outer functor is essentially surjective. A model-
independent algebraic presentation theorem is now also proved: every relation-
preserving raw-cell interpretation into any category descends to a functor
and has a unique compatible quotient lift. The result now extends to common-
universe nerves in every degree, and natural transformations/isomorphisms of
descended interpretations induce genuine simplicial homotopies. An independent
derived or hammock characterization, weak-equivalence packaging, and the
global complete-Segal/Rezk theorem remain open. The currently proved
`PresentedDwyerKanCore` combines all project-local object and mapping
conditions. An independent right-associated linear hammock syntax now also
gives an equivalent mapping category and direct target-nerve homotopy
equivalence, packaged with outer essential surjectivity in
`LinearHammockDwyerKanCore`. Every arbitrary-height vertical row grid is now
equivalent to a linear-hammock nerve simplex, with exact rows, adjacent edges,
endpoint equations and round trips. Fixed-shape aligned multi-column cells now
have explicit widths, executable horizontal append, exact identity/vertical-composition
interpretation, and arbitrary-height grid reconstruction with exact rows and
edges. Elementary forward identity/composition column refinements are now
executable, with exact signed-width change, quotient interpretation, inverse
round trips, and prefix stability. Marked unit/counit pairs now have the same
executable insertion/deletion, signed-width, semantic-isomorphism, and prefix-
stable inverse laws. Every refinement now has an executable reverse and unified
semantic isomorphism; common-refinement spans form a setoid and row quotient,
and quotient equality soundly yields semantic isomorphism without object
equality. The zero-truncated part is closed: the thin common-refinement
groupoid is categorically equivalent
to the discrete row quotient, and the nerve map has an explicit simplicial
homotopy inverse. The non-thin semantic path groupoid
and its faithful, object-essentially-surjective nerve map now compile, with
exact refinement-edge interpretation and full zero-truncation onto the thin
groupoid. Its exact refinement-generated quotient-cell image is now a
subgroupoid equivalent to the path groupoid, with a faithful inclusion into
the full linear mapping category and a strictly factored semantic nerve map.
The aligned-cell-augmented non-groupoidal path category now adds arbitrary
pointwise raw cells, contains every source 2-cell in canonical one-column form,
and strictly extends the refinement path nerve. What remains is normalization
of every presented quotient 2-cell into these generated paths, critical-pair
coherence, and reduced-hammock invariance. These
layers do not add `Equiv α β → α = β` and are not a complete presheaf model.
