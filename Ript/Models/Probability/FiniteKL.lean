import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Ript.Models.FiniteDistribution
import Ript.Models.Probability.StochFunctor

/-!
# Kullback--Leibler divergence for exact finite distributions

This file gives the executable rational distributions of
`Ript.Models.FiniteDistribution` their canonical discrete measure semantics and
then specializes Mathlib's measure-theoretic Kullback--Leibler divergence.

The definition deliberately takes values in `ℝ≥0∞`.  Consequently it retains
the mathematically important boundary case: if the first distribution assigns
positive mass where the second assigns zero mass, the divergence is `∞` rather
than an arbitrary finite sentinel.  The source distributions and stochastic
channels remain exact rational data; noncomputability enters only through the
analytic KL interpretation.
-/

set_option autoImplicit false

namespace Ript.Models.Probability.FiniteKL

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Probability.StochFunctor

universe u

noncomputable section

/-- The canonical discrete probability measure represented by an exact finite
distribution. -/
def distributionMeasure {X : Object.{u}} (p : FinDist X) : @Measure X ⊤ := by
  letI : MeasurableSpace X := ⊤
  exact ∑ x : X, (p.prob x : ℝ≥0∞) • Measure.dirac x

/-- Evaluation of the semantic distribution measure on an arbitrary set. -/
theorem distributionMeasure_apply {X : Object.{u}} (p : FinDist X)
    (s : Set X) :
    distributionMeasure p s =
      ∑ x : X, (p.prob x : ℝ≥0∞) * s.indicator 1 x := by
  simp [distributionMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.of_discrete, smul_eq_mul]

/-- The semantic measure retains the source distribution's normalization. -/
theorem distributionMeasure_univ {X : Object.{u}} (p : FinDist X) :
    distributionMeasure p Set.univ = 1 := by
  rw [distributionMeasure_apply]
  simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  rw [ennreal_coe_nnrat_fintype_sum, p.normalized]
  exact ennreal_coe_nnrat_one

/-- The semantic measure has total mass one. -/
instance distributionMeasureIsProbability {X : Object.{u}} (p : FinDist X) :
    IsProbabilityMeasure (distributionMeasure p) := by
  exact ⟨distributionMeasure_univ p⟩

/-- Singleton mass in the semantic measure is exactly the source rational
probability, embedded in `ℝ≥0∞`. -/
@[simp]
theorem distributionMeasure_singleton {X : Object.{u}} (p : FinDist X) (x : X) :
    distributionMeasure p {x} = (p.prob x : ℝ≥0∞) := by
  rw [distributionMeasure_apply]
  simp [Set.indicator, eq_comm]

/-- Integrating over the semantic distribution measure is the corresponding
finite weighted sum. -/
theorem lintegral_distributionMeasure {X : Object.{u}} (p : FinDist X)
    (g : X → ℝ≥0∞) :
    @lintegral X ⊤ (distributionMeasure p) g =
      ∑ x : X, (p.prob x : ℝ≥0∞) * g x := by
  simp [distributionMeasure, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac]

/-- Real-valued integration over a semantic finite distribution is the
corresponding probability-weighted finite sum. -/
theorem integral_distributionMeasure {X : Object.{u}} (p : FinDist X)
    (g : X → ℝ) :
    letI : MeasurableSpace X := ⊤
    ∫ x, g x ∂distributionMeasure p =
      ∑ x : X, (p.prob x : ℝ) * g x := by
  let _ : MeasurableSpace X := ⊤
  rw [distributionMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x _
    simp only [← ENNReal.coe_nnratCast, ENNReal.coe_toReal,
      NNRat.cast_def, NNReal.coe_div, NNReal.coe_natCast]
  · intro x _
    apply (integrable_dirac (by finiteness)).smul_measure
    exact (ENNReal.coe_ne_top : (p.prob x : ℝ≥0∞) ≠ ∞)

/-- The discrete measure interpretation loses no information. -/
theorem distributionMeasure_injective {X : Object.{u}} :
    Function.Injective (@distributionMeasure X) := by
  intro p q hpq
  apply FinDist.ext
  intro x
  have hx := congrArg (fun μ : @Measure X ⊤ ↦ μ {x}) hpq
  simp only [distributionMeasure_singleton] at hx
  apply NNRat.cast_injective (α := NNReal)
  apply ENNReal.coe_injective
  exact hx

/-- An exact nonnegative rational has zero semantic mass exactly when it is
zero in the source representation. -/
theorem ennreal_coe_nnrat_eq_zero_iff (a : ℚ≥0) :
    (a : ℝ≥0∞) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply NNRat.cast_injective (α := NNReal)
    apply ENNReal.coe_injective
    rw [ENNReal.coe_nnratCast, ENNReal.coe_nnratCast]
    simpa only [ennreal_coe_nnrat_zero] using h
  · rintro rfl
    exact ennreal_coe_nnrat_zero

/-- On a finite discrete space, absolute continuity is exactly containment of
the nonzero support. -/
theorem distributionMeasure_absolutelyContinuous_iff
    {X : Object.{u}} {p q : FinDist X} :
    distributionMeasure p ≪ distributionMeasure q ↔
      ∀ x, q.prob x = 0 → p.prob x = 0 := by
  constructor
  · intro hpq x hqx
    have hpx : distributionMeasure p {x} = 0 := hpq (by
      rw [distributionMeasure_singleton, ennreal_coe_nnrat_eq_zero_iff]
      exact hqx)
    rw [distributionMeasure_singleton, ennreal_coe_nnrat_eq_zero_iff] at hpx
    exact hpx
  · intro hpq s hqs
    rw [measure_null_iff_singleton (Set.to_countable s)] at hqs ⊢
    intro x hxs
    rw [distributionMeasure_singleton, ennreal_coe_nnrat_eq_zero_iff]
    apply hpq x
    rw [← ennreal_coe_nnrat_eq_zero_iff,
      ← distributionMeasure_singleton]
    exact hqs x hxs

/-- Semantic kernel composition is exactly the executable pushforward of a
finite distribution. -/
theorem distributionMeasure_push {X Y : Object.{u}} (p : FinDist X)
    (channel : FinStoch X Y) :
    toKernel channel ∘ₘ distributionMeasure p =
      distributionMeasure (p.push channel) := by
  apply @Measure.ext_of_singleton Y ⊤ (by infer_instance)
  intro y
  rw [Measure.bind_apply MeasurableSpace.measurableSet_top
    (Kernel.aemeasurable _)]
  simp only [toKernel_apply, rowMeasure_singleton,
    distributionMeasure_singleton, FinDist.push_apply]
  rw [lintegral_distributionMeasure]
  rw [← ennreal_coe_nnrat_fintype_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact (ennreal_coe_nnrat_mul _ _).symm

/-- Kullback--Leibler divergence of exact finite distributions, with the
standard extended-nonnegative-real boundary semantics. -/
def finiteKL {X : Object.{u}} (p q : FinDist X) : ℝ≥0∞ :=
  InformationTheory.klDiv (distributionMeasure p) (distributionMeasure q)

/-- The pointwise Radon--Nikodym density of `p` relative to `q`, expressed
directly from their exact rational probability masses. -/
def densityRatio {X : Object.{u}} (p q : FinDist X) (x : X) : ℝ≥0∞ :=
  (p.prob x : ℝ≥0∞) / (q.prob x : ℝ≥0∞)

/-- The explicit finite f-divergence summand used by the extended-real KL
formula. -/
def finiteKLTerm {X : Object.{u}} (p q : FinDist X) (x : X) : ℝ≥0∞ :=
  (q.prob x : ℝ≥0∞) *
    ENNReal.ofReal (InformationTheory.klFun (densityRatio p q x).toReal)

/-- The classical real-valued KL summand.  Lean's real logarithm satisfies
`log 0 = 0`, so the conventional `0 * log 0 = 0` boundary needs no separate
branch. -/
def finiteKLRealTerm {X : Object.{u}} (p q : FinDist X) (x : X) : ℝ :=
  (p.prob x : ℝ) * Real.log ((p.prob x : ℝ) / (q.prob x : ℝ))

/-- Absolute continuity identifies the first discrete measure as the second
measure weighted by the explicit pointwise density ratio. -/
theorem distributionMeasure_withDensity_densityRatio {X : Object.{u}}
    {p q : FinDist X}
    (h_ac : distributionMeasure p ≪ distributionMeasure q) :
    (distributionMeasure q).withDensity (densityRatio p q) =
      distributionMeasure p := by
  let _ : MeasurableSpace X := ⊤
  apply @Measure.ext_of_singleton X ⊤ (by infer_instance)
  intro x
  rw [withDensity_apply _ MeasurableSet.of_discrete,
    lintegral_singleton, distributionMeasure_singleton,
    distributionMeasure_singleton]
  apply ENNReal.div_mul_cancel'
  · intro hqx
    rw [ennreal_coe_nnrat_eq_zero_iff] at hqx
    rw [ennreal_coe_nnrat_eq_zero_iff]
    exact (distributionMeasure_absolutelyContinuous_iff.mp h_ac) x hqx
  · intro hqx
    exact False.elim ((ENNReal.coe_ne_top : (q.prob x : ℝ≥0∞) ≠ ∞) hqx)

/-- The Radon--Nikodym derivative of two exact finite distributions is their
pointwise rational mass ratio, almost everywhere under the reference measure. -/
theorem rnDeriv_distributionMeasure_ae {X : Object.{u}} {p q : FinDist X}
    (h_ac : distributionMeasure p ≪ distributionMeasure q) :
    (distributionMeasure p).rnDeriv (distributionMeasure q) =ᵐ[distributionMeasure q]
      densityRatio p q := by
  let _ : MeasurableSpace X := ⊤
  rw [← distributionMeasure_withDensity_densityRatio h_ac]
  exact Measure.rnDeriv_withDensity _ Measurable.of_discrete

/-- The log-likelihood ratio is the logarithm of the exact pointwise mass
ratio, almost everywhere under the first distribution. -/
theorem llr_distributionMeasure_ae {X : Object.{u}} {p q : FinDist X}
    (h_ac : distributionMeasure p ≪ distributionMeasure q) :
    llr (distributionMeasure p) (distributionMeasure q) =ᵐ[distributionMeasure p]
      fun x => Real.log (densityRatio p q x).toReal := by
  apply h_ac.ae_eq
  filter_upwards [rnDeriv_distributionMeasure_ae h_ac] with x hx
  simp only [llr, hx]

/-- **Explicit finite KL formula.** Whenever the support of `p` is contained
in that of `q`, the measure-theoretic KL divergence is exactly a finite sum of
the pointwise f-divergence terms. -/
theorem finiteKL_eq_sum_of_absolutelyContinuous {X : Object.{u}}
    {p q : FinDist X}
    (h_ac : distributionMeasure p ≪ distributionMeasure q) :
    finiteKL p q = ∑ x : X, finiteKLTerm p q x := by
  rw [finiteKL, InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac]
  rw [lintegral_congr_ae]
  · rw [lintegral_distributionMeasure]
    rfl
  · filter_upwards [rnDeriv_distributionMeasure_ae h_ac] with x hx
    simp only [hx]

/-- Under the same support condition, the real value of finite KL is the
classical finite sum `sum_x p(x) log (p(x) / q(x))`. -/
theorem finiteKL_toReal_eq_sum_of_absolutelyContinuous {X : Object.{u}}
    {p q : FinDist X}
    (h_ac : distributionMeasure p ≪ distributionMeasure q) :
    (finiteKL p q).toReal = ∑ x : X, finiteKLRealTerm p q x := by
  rw [finiteKL, InformationTheory.toReal_klDiv_of_measure_eq h_ac]
  · rw [integral_congr_ae (llr_distributionMeasure_ae h_ac),
      integral_distributionMeasure]
    apply Finset.sum_congr rfl
    intro x _
    simp only [finiteKLRealTerm, densityRatio, ENNReal.toReal_div]
    congr 2
  · rw [distributionMeasure_univ, distributionMeasure_univ]

/-- A support-containment hypothesis stated directly on exact rational masses
is sufficient for the explicit extended-real finite sum. -/
theorem finiteKL_eq_sum_of_support {X : Object.{u}} {p q : FinDist X}
    (h_support : ∀ x, q.prob x = 0 → p.prob x = 0) :
    finiteKL p q = ∑ x : X, finiteKLTerm p q x := by
  apply finiteKL_eq_sum_of_absolutelyContinuous
  exact distributionMeasure_absolutelyContinuous_iff.mpr h_support

/-- With a full-support reference distribution, the classical real finite-sum
formula is always available. -/
theorem finiteKL_toReal_eq_sum_of_fullSupport {X : Object.{u}} {p q : FinDist X}
    (h_full : ∀ x, q.prob x ≠ 0) :
    (finiteKL p q).toReal = ∑ x : X, finiteKLRealTerm p q x := by
  apply finiteKL_toReal_eq_sum_of_absolutelyContinuous
  rw [distributionMeasure_absolutelyContinuous_iff]
  intro x hqx
  exact False.elim (h_full x hqx)

/-- Absolute continuity rules out the infinite boundary of finite KL. -/
theorem finiteKL_ne_top_of_absolutelyContinuous {X : Object.{u}}
    {p q : FinDist X}
    (h_ac : distributionMeasure p ≪ distributionMeasure q) :
    finiteKL p q ≠ ∞ := by
  rw [finiteKL_eq_sum_of_absolutelyContinuous h_ac]
  simp [finiteKLTerm]
  intro x
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

/-- A distribution has zero KL divergence from itself. -/
@[simp]
theorem finiteKL_self {X : Object.{u}} (p : FinDist X) : finiteKL p p = 0 := by
  exact InformationTheory.klDiv_self _

/-- Finite KL divergence separates exact finite distributions. -/
theorem finiteKL_eq_zero_iff {X : Object.{u}} {p q : FinDist X} :
    finiteKL p q = 0 ↔ p = q := by
  rw [finiteKL, InformationTheory.klDiv_eq_zero_iff]
  exact distributionMeasure_injective.eq_iff

/-- A support violation forces infinite KL divergence: assigning positive
mass where the reference distribution assigns zero mass breaks absolute
continuity. -/
theorem finiteKL_eq_top_of_support_violation {X : Object.{u}}
    {p q : FinDist X}
    (h : ∃ x, p.prob x ≠ 0 ∧ q.prob x = 0) : finiteKL p q = ∞ := by
  apply InformationTheory.klDiv_of_not_ac
  rw [distributionMeasure_absolutelyContinuous_iff]
  intro hpq
  obtain ⟨x, hpx, hqx⟩ := h
  exact hpx (hpq x hqx)

/-- Finite KL reaches `∞` exactly when the first distribution assigns nonzero
mass to a point on which the reference distribution has zero mass. -/
theorem finiteKL_eq_top_iff_support_violation {X : Object.{u}}
    {p q : FinDist X} :
    finiteKL p q = ∞ ↔ ∃ x, p.prob x ≠ 0 ∧ q.prob x = 0 := by
  constructor
  · intro h_top
    by_contra h_violation
    push Not at h_violation
    have h_ac : distributionMeasure p ≪ distributionMeasure q := by
      rw [distributionMeasure_absolutelyContinuous_iff]
      intro x hqx
      by_contra hpx
      exact h_violation x hpx hqx
    exact (finiteKL_ne_top_of_absolutelyContinuous h_ac) h_top
  · exact finiteKL_eq_top_of_support_violation

/-- Distinct point masses exhibit the KL boundary behavior explicitly: their
divergence is infinite, while equal point masses have divergence zero. -/
theorem finiteKL_pure {X : Object.{u}} (x y : X) :
    finiteKL (FinDist.pure x) (FinDist.pure y) =
      if x = y then 0 else ∞ := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [if_neg hxy]
    apply finiteKL_eq_top_of_support_violation
    refine ⟨x, ?_, ?_⟩
    · simp
    · simp [Ne.symm hxy]

/-- **Finite KL data processing.** Applying any exact finite stochastic
channel to both distributions cannot increase their KL divergence. -/
theorem finiteKL_dataProcessing {X Y : Object.{u}} (channel : FinStoch X Y)
    (p q : FinDist X) :
    finiteKL (p.push channel) (q.push channel) ≤ finiteKL p q := by
  unfold finiteKL
  rw [← distributionMeasure_push p channel,
    ← distributionMeasure_push q channel]
  exact InformationTheory.klDiv_comp_right_le
    (distributionMeasure p) (distributionMeasure q) (toKernel channel)

end

end Ript.Models.Probability.FiniteKL
