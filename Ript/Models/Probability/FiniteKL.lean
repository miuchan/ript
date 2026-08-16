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
