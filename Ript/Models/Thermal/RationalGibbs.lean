import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Ript.Models.Thermal.Gibbs

/-!
# Exact rationality criterion for finite Gibbs spectra

This module classifies when an independently specified finite real energy
spectrum has an exact nonnegative-rational Gibbs distribution.  After fixing
one reference microstate, normalized Gibbs probabilities are rational exactly
when every Boltzmann weight ratio to that reference is a positive rational
number.

The criterion is gauge invariant and applies to arbitrary real energies.  A
separate constructor starts from explicit positive rational Boltzmann weights,
builds their logarithmic real spectrum, and recovers their exact normalized
`FinDist`.  This gives a computably checkable sufficient family without
pretending that equality of arbitrary real exponentials is decidable.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

noncomputable section

namespace FiniteGibbsData

/-- An arbitrary real Gibbs spectrum has exact rational probabilities when
its normalized probabilities are the real coercions of one exact `FinDist`. -/
def HasRationalProbabilities {X : Object.{u}} (data : FiniteGibbsData X) : Prop :=
  ∃ state : FinDist X, ∀ x, data.probability x = (state.prob x : ℝ)

/-- Relative to a chosen reference microstate, all Boltzmann ratios are
positive rational numbers.  The exponential equation is stated directly in
terms of the independently supplied real energies. -/
def HasRationalBoltzmannRatiosAt {X : Object.{u}}
    (data : FiniteGibbsData X) (reference : X) : Prop :=
  ∃ ratios : X → ℚ≥0,
    (∀ x, 0 < ratios x) ∧
    ∀ x, Real.exp (-data.inverseTemperature *
      (data.energy x - data.energy reference)) = (ratios x : ℝ)

/-- Normalize a positive finite family of rational weights into an exact
executable distribution. -/
def normalizedRationalWeights {X : Object.{u}} (weights : X → ℚ≥0)
    (nonempty : Nonempty X) (positive : ∀ x, 0 < weights x) : FinDist X where
  prob x := weights x / ∑ y, weights y
  normalized := by
    classical
    have hsum_pos : 0 < ∑ y : X, weights y := by
      apply Finset.sum_pos'
      · intro x _
        exact (positive x).le
      · let reference := Classical.choice nonempty
        exact ⟨reference, Finset.mem_univ reference, positive reference⟩
    rw [← Finset.sum_div, div_self (ne_of_gt hsum_pos)]

/-- Entrywise formula for normalized rational weights. -/
@[simp]
theorem normalizedRationalWeights_prob {X : Object.{u}}
    (weights : X → ℚ≥0) (nonempty : Nonempty X)
    (positive : ∀ x, 0 < weights x) (x : X) :
    (normalizedRationalWeights weights nonempty positive).prob x =
      weights x / ∑ y, weights y := rfl

/-- Taking a ratio of normalized Gibbs probabilities cancels the common
partition function. -/
theorem probability_ratio {X : Object.{u}} (data : FiniteGibbsData X)
    (x reference : X) :
    data.probability x / data.probability reference =
      data.weight x / data.weight reference := by
  unfold probability
  exact div_div_div_cancel_right₀ data.partitionFunction_ne_zero _ _

/-- A ratio of Boltzmann weights is the exponential of the corresponding
energy gap, so the rationality criterion is independent of the energy gauge. -/
theorem weight_ratio_eq_exp_energyGap {X : Object.{u}}
    (data : FiniteGibbsData X) (x reference : X) :
    data.weight x / data.weight reference =
      Real.exp (-data.inverseTemperature *
        (data.energy x - data.energy reference)) := by
  unfold weight
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Exact classification theorem: a finite real Gibbs spectrum has rational
normalized probabilities iff all Boltzmann ratios to any fixed reference
microstate are positive rationals. -/
theorem hasRationalProbabilities_iff_hasRationalBoltzmannRatiosAt
    {X : Object.{u}} (data : FiniteGibbsData X) (reference : X) :
    data.HasRationalProbabilities ↔
      data.HasRationalBoltzmannRatiosAt reference := by
  constructor
  · rintro ⟨state, hstate⟩
    have hstate_pos (x : X) : 0 < state.prob x := by
      have hstate_real_pos : 0 < (state.prob x : ℝ) := by
        rw [← hstate x]
        exact data.probability_pos x
      exact NNRat.cast_pos.mp hstate_real_pos
    refine ⟨fun x ↦ state.prob x / state.prob reference,
      fun x ↦ div_pos (hstate_pos x) (hstate_pos reference), ?_⟩
    intro x
    rw [← data.weight_ratio_eq_exp_energyGap x reference,
      ← data.probability_ratio x reference,
      hstate x, hstate reference]
    norm_cast
  · rintro ⟨ratios, hratios_pos, hratios⟩
    have hweight_ratio (x : X) :
        data.weight x / data.weight reference = (ratios x : ℝ) := by
      rw [data.weight_ratio_eq_exp_energyGap x reference]
      exact hratios x
    have hweight_eq (x : X) :
        data.weight x = (ratios x : ℝ) * data.weight reference :=
      (div_eq_iff (ne_of_gt (data.weight_pos reference))).mp
        (hweight_ratio x)
    have hpartition :
        data.partitionFunction =
          ((∑ x : X, ratios x : ℚ≥0) : ℝ) * data.weight reference := by
      rw [partitionFunction]
      calc
        (∑ x : X, data.weight x) =
            ∑ x : X, (ratios x : ℝ) * data.weight reference := by
          apply Fintype.sum_congr
          intro x
          exact hweight_eq x
        _ = ((∑ x : X, ratios x : ℚ≥0) : ℝ) *
            data.weight reference := by
          rw [← Finset.sum_mul, ← NNRat.cast_sum]
    have hsum_pos : 0 < ∑ x : X, ratios x := by
      apply Finset.sum_pos'
      · intro x _
        exact (hratios_pos x).le
      · exact ⟨reference, Finset.mem_univ reference, hratios_pos reference⟩
    refine ⟨normalizedRationalWeights ratios data.nonempty hratios_pos, ?_⟩
    intro x
    rw [probability, hweight_eq, hpartition,
      normalizedRationalWeights_prob]
    rw [mul_div_mul_right _ _ (ne_of_gt (data.weight_pos reference))]
    norm_cast

/-- Build real Gibbs data from explicit positive rational Boltzmann weights.
The energy gauge is chosen so each unnormalized weight is exactly the supplied
rational number. -/
def ofPositiveRationalWeights {X : Object.{u}} (weights : X → ℚ≥0)
    (nonempty : Nonempty X) (_positive : ∀ x, 0 < weights x)
    (β : ℝ) (hβ : 0 < β) : FiniteGibbsData X where
  energy x := -Real.log (weights x : ℝ) / β
  inverseTemperature := β
  inverseTemperature_pos := hβ
  nonempty := nonempty

/-- The logarithmic spectrum constructor recovers every supplied rational
Boltzmann weight exactly. -/
theorem ofPositiveRationalWeights_weight {X : Object.{u}}
    (weights : X → ℚ≥0) (nonempty : Nonempty X)
    (positive : ∀ x, 0 < weights x) (β : ℝ) (hβ : 0 < β) (x : X) :
    (ofPositiveRationalWeights weights nonempty positive β hβ).weight x =
      (weights x : ℝ) := by
  have hweight_pos : 0 < (weights x : ℝ) := NNRat.cast_pos.mpr (positive x)
  unfold weight ofPositiveRationalWeights
  rw [show -β * (-Real.log (weights x : ℝ) / β) =
      Real.log (weights x : ℝ) by
    field_simp [ne_of_gt hβ]]
  exact Real.exp_log hweight_pos

/-- The partition function of a rational-weight-generated spectrum is the
real coercion of the exact rational weight sum. -/
theorem ofPositiveRationalWeights_partitionFunction {X : Object.{u}}
    (weights : X → ℚ≥0) (nonempty : Nonempty X)
    (positive : ∀ x, 0 < weights x) (β : ℝ) (hβ : 0 < β) :
    (ofPositiveRationalWeights weights nonempty positive β hβ).partitionFunction =
      ((∑ x : X, weights x : ℚ≥0) : ℝ) := by
  rw [partitionFunction]
  simp_rw [ofPositiveRationalWeights_weight weights nonempty positive β hβ]
  exact (NNRat.cast_sum Finset.univ weights).symm

/-- The normalized analytic Gibbs probability of the generated spectrum is
exactly the coercion of the normalized rational distribution. -/
theorem ofPositiveRationalWeights_probability {X : Object.{u}}
    (weights : X → ℚ≥0) (nonempty : Nonempty X)
    (positive : ∀ x, 0 < weights x) (β : ℝ) (hβ : 0 < β) (x : X) :
    (ofPositiveRationalWeights weights nonempty positive β hβ).probability x =
      ((normalizedRationalWeights weights nonempty positive).prob x : ℝ) := by
  rw [probability,
    ofPositiveRationalWeights_weight weights nonempty positive β hβ,
    ofPositiveRationalWeights_partitionFunction weights nonempty positive β hβ,
    normalizedRationalWeights_prob]
  norm_cast

/-- Every spectrum generated from explicit positive rational weights satisfies
the exact rational-probability side of the classification theorem. -/
theorem ofPositiveRationalWeights_hasRationalProbabilities
    {X : Object.{u}} (weights : X → ℚ≥0) (nonempty : Nonempty X)
    (positive : ∀ x, 0 < weights x) (β : ℝ) (hβ : 0 < β) :
    HasRationalProbabilities
      (ofPositiveRationalWeights weights nonempty positive β hβ) :=
  ⟨normalizedRationalWeights weights nonempty positive,
    ofPositiveRationalWeights_probability weights nonempty positive β hβ⟩

end FiniteGibbsData

end

end Ript.Models.Thermal
