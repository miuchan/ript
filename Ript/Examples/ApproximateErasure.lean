import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Ript.Examples.SimpleThermalModel

/-!
# Exact finite approximate erasure

This module refines the exact Boolean Landauer example to an executable target
with rational error probability `ε ≤ 1/2`.  The target stores `false` with
probability `1 - ε` and `true` with probability `ε`.

Its Shannon entropy is exactly Mathlib's binary entropy `binEntropy ε`, so its
excess free energy above the uniform zero-energy equilibrium is

`(log 2 - binEntropy ε) / β`.

The module proves this cost is nonnegative and decreases as the allowed error
increases.  It then specializes both the product-endpoint and
correlation-corrected work-assisted transition theorems.  These are necessary
bounds for supplied transition certificates; no transition-existence or
saturation claim is made.
-/

set_option autoImplicit false

namespace Ript.Examples.SimpleThermalModel

open Ript.Models.FiniteDistribution
open Ript.Models.Thermal

/-- Exact approximate erasure target with rational error probability at most
one half.  `false` is the intended erased value and `true` is the error. -/
def approximateErasedBit (ε : ℚ≥0)
    (hε : ε ≤ (1 : ℚ≥0) / 2) : FinDist thermalBit.system where
  prob value := if (show Bool from value) = false then 1 - ε else ε
  normalized := by
    change (∑ value : Bool, if value = false then 1 - ε else ε) = 1
    rw [Fintype.sum_bool]
    simp only [↓reduceIte]
    have hhalfOne : (1 : ℚ≥0) / 2 ≤ 1 := by norm_num
    simpa using add_tsub_cancel_of_le (hε.trans hhalfOne)

/-- The intended erased value has exact probability `1 - ε`. -/
@[simp]
theorem approximateErasedBit_prob_false (ε : ℚ≥0)
    (hε : ε ≤ (1 : ℚ≥0) / 2) :
    (approximateErasedBit ε hε).prob false = 1 - ε := by
  rfl

/-- The error event has exact probability `ε`. -/
@[simp]
theorem approximateErasedBit_prob_true (ε : ℚ≥0)
    (hε : ε ≤ (1 : ℚ≥0) / 2) :
    (approximateErasedBit ε hε).prob true = ε := by
  rfl

/-- Zero error recovers the exact erased state. -/
theorem approximateErasedBit_zero
    (hzero : (0 : ℚ≥0) ≤ (1 : ℚ≥0) / 2) :
    approximateErasedBit 0 hzero = erasedBit := by
  apply FinDist.ext
  intro value
  change Bool at value
  cases value
  · rw [approximateErasedBit_prob_false]
    change 1 - 0 = if (false : Bool) = false then 1 else 0
    rw [if_pos rfl]
    simp
  · rw [approximateErasedBit_prob_true]
    change 0 = if (false : Bool) = true then 1 else 0
    rw [if_neg (by decide)]

/-- Error one half recovers the uniform equilibrium state. -/
theorem approximateErasedBit_half
    (hhalf : (1 : ℚ≥0) / 2 ≤ (1 : ℚ≥0) / 2) :
    approximateErasedBit ((1 : ℚ≥0) / 2) hhalf = fairEquilibrium := by
  have hsub : (1 - (1 : ℚ≥0) / 2 : ℚ≥0) = (1 : ℚ≥0) / 2 := by
    apply NNRat.coe_injective
    rw [NNRat.coe_sub (by norm_num)]
    norm_num
  apply FinDist.ext
  intro value
  change Bool at value
  cases value
  · rw [approximateErasedBit_prob_false]
    change 1 - (1 : ℚ≥0) / 2 = (1 : ℚ≥0) / 2
    exact hsub
  · rw [approximateErasedBit_prob_true]
    rfl

/-- One-quarter error lies in the admitted approximate-erasure interval. -/
theorem quarterError_le_half :
    (1 : ℚ≥0) / 4 ≤ (1 : ℚ≥0) / 2 := by
  apply NNRat.coe_le_coe.mp
  norm_num

/-- Analytic free-energy price of approximate Boolean erasure at inverse
temperature `β` and exact rational error `ε`. -/
noncomputable def approximateErasureCost (β : ℝ) (ε : ℚ≥0) : ℝ :=
  (Real.log 2 - Real.binEntropy (ε : ℝ)) / β

/-- Approximate-erasure cost is nonnegative at positive inverse temperature. -/
theorem approximateErasureCost_nonneg (β : ℝ) (hβ : 0 < β)
    (ε : ℚ≥0) : 0 ≤ approximateErasureCost β ε := by
  exact div_nonneg (sub_nonneg.mpr Real.binEntropy_le_log_two) hβ.le

/-- At zero error, approximate-erasure cost is the exact Landauer value. -/
@[simp]
theorem approximateErasureCost_zero (β : ℝ) :
    approximateErasureCost β 0 = Real.log 2 / β := by
  simp [approximateErasureCost]

/-- At error one half, the target is equilibrium and its excess-free-energy
cost vanishes. -/
@[simp]
theorem approximateErasureCost_half (β : ℝ) :
    approximateErasureCost β (2 : ℚ≥0)⁻¹ = 0 := by
  unfold approximateErasureCost
  have hcast : (((2 : ℚ≥0)⁻¹ : ℚ≥0) : ℝ) = (2 : ℝ)⁻¹ := by
    norm_num
  rw [hcast, Real.binEntropy_two_inv]
  simp

/-- Allowing more error between zero and one half cannot increase the exact
free-energy cost of approximate erasure. -/
theorem approximateErasureCost_antitone (β : ℝ) (hβ : 0 < β)
    {ε₁ ε₂ : ℚ≥0} (hε₁ : ε₁ ≤ (1 : ℚ≥0) / 2)
    (hε₂ : ε₂ ≤ (1 : ℚ≥0) / 2) (hε : ε₁ ≤ ε₂) :
    approximateErasureCost β ε₂ ≤ approximateErasureCost β ε₁ := by
  have hmem₁ : (ε₁ : ℝ) ∈ Set.Icc 0 (2 : ℝ)⁻¹ := by
    constructor
    · positivity
    · have hcast : (ε₁ : ℝ) ≤ (((1 : ℚ≥0) / 2 : ℚ≥0) : ℝ) := by
        exact_mod_cast hε₁
      norm_num at hcast ⊢
      exact hcast
  have hmem₂ : (ε₂ : ℝ) ∈ Set.Icc 0 (2 : ℝ)⁻¹ := by
    constructor
    · positivity
    · have hcast : (ε₂ : ℝ) ≤ (((1 : ℚ≥0) / 2 : ℚ≥0) : ℝ) := by
        exact_mod_cast hε₂
      norm_num at hcast ⊢
      exact hcast
  have hεReal : (ε₁ : ℝ) ≤ (ε₂ : ℝ) := by
    exact_mod_cast hε
  have hentropy : Real.binEntropy (ε₁ : ℝ) ≤
      Real.binEntropy (ε₂ : ℝ) :=
    Real.binEntropy_strictMonoOn.monotoneOn hmem₁ hmem₂ hεReal
  unfold approximateErasureCost
  rw [div_le_div_iff_of_pos_right hβ]
  linarith

/-- Shannon entropy of the exact approximate-erasure target is precisely the
binary entropy of its error probability. -/
@[simp]
theorem approximateErasedBit_entropy (ε : ℚ≥0)
    (hε : ε ≤ (1 : ℚ≥0) / 2) (β : ℝ) (hβ : 0 < β) :
    (gibbsThermalBitAt β hβ).entropy (approximateErasedBit ε hε) =
      Real.binEntropy (ε : ℝ) := by
  unfold GibbsThermalObject.entropy
  change -(∑ value : Bool,
    ((approximateErasedBit ε hε).prob value : ℝ) *
      Real.log ((approximateErasedBit ε hε).prob value : ℝ)) = _
  rw [Fintype.sum_bool, approximateErasedBit_prob_true,
    approximateErasedBit_prob_false]
  have hhalfOne : (1 : ℚ≥0) / 2 ≤ 1 := by norm_num
  have hεOne : ε ≤ (1 : ℚ≥0) := hε.trans hhalfOne
  have hcast : ((1 - ε : ℚ≥0) : ℝ) = 1 - (ε : ℝ) := by
    have hsum : (1 - ε : ℚ≥0) + ε = 1 :=
      tsub_add_cancel_of_le hεOne
    have hsumReal : ((1 - ε : ℚ≥0) : ℝ) + (ε : ℝ) = 1 := by
      exact_mod_cast hsum
    linarith
  rw [hcast, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold Real.negMulLog
  ring

/-- The exact approximate-erasure target has excess free energy equal to the
binary-entropy deficit divided by inverse temperature. -/
theorem approximateErasedBit_freeEnergyGap (ε : ℚ≥0)
    (hε : ε ≤ (1 : ℚ≥0) / 2) (β : ℝ) (hβ : 0 < β) :
    (gibbsThermalBitAt β hβ).freeEnergyGap
        (approximateErasedBit ε hε) =
      approximateErasureCost β ε := by
  unfold GibbsThermalObject.freeEnergyGap
    GibbsThermalObject.nonequilibriumFreeEnergy approximateErasureCost
  rw [thermalBitAt_meanEnergy β hβ (approximateErasedBit ε hε),
    approximateErasedBit_entropy ε hε β hβ,
    thermalBitAt_equilibriumFreeEnergy β hβ]
  change 0 - Real.binEntropy (ε : ℝ) / β - (-Real.log 2 / β) =
    (Real.log 2 - Real.binEntropy (ε : ℝ)) / β
  ring

/-- Product-endpoint approximate erasure requires at least the exact
binary-entropy-deficit amount of battery free energy. -/
theorem thermalBit_approximate_erasure_landauer_freeEnergy_bound
    (ε : ℚ≥0) (hε : ε ≤ (1 : ℚ≥0) / 2)
    (β : ℝ) (hβ : 0 < β) {battery : GibbsThermalObject}
    (transition : WorkAssistedTransition
      (gibbsThermalBitAt β hβ) (gibbsThermalBitAt β hβ) battery)
    (hInitial : transition.initialSystem = fairEquilibrium)
    (hFinal : transition.finalSystem = approximateErasedBit ε hε) :
    approximateErasureCost β ε ≤
      transition.batteryFreeEnergyDecrease := by
  have hbound := transition.landauer_freeEnergy_bound
  unfold WorkAssistedTransition.systemFreeEnergyIncrease at hbound
  rw [hInitial, hFinal, approximateErasedBit_freeEnergyGap ε hε β hβ,
    thermalBitAt_fair_freeEnergyGap β hβ, sub_zero] at hbound
  exact hbound

/-- Entropy-neutral battery form of the product-endpoint approximate-erasure
Landauer work bound. -/
theorem thermalBit_approximate_erasure_landauer_work_bound
    (ε : ℚ≥0) (hε : ε ≤ (1 : ℚ≥0) / 2)
    (β : ℝ) (hβ : 0 < β) {battery : GibbsThermalObject}
    (transition : WorkAssistedTransition
      (gibbsThermalBitAt β hβ) (gibbsThermalBitAt β hβ) battery)
    (hInitial : transition.initialSystem = fairEquilibrium)
    (hFinal : transition.finalSystem = approximateErasedBit ε hε)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    approximateErasureCost β ε ≤ transition.batteryEnergyDecrease := by
  have hbound := transition.landauer_work_bound hEntropy
  unfold WorkAssistedTransition.systemFreeEnergyIncrease at hbound
  rw [hInitial, hFinal, approximateErasedBit_freeEnergyGap ε hε β hβ,
    thermalBitAt_fair_freeEnergyGap β hβ, sub_zero] at hbound
  exact hbound

/-- Correlation-corrected approximate erasure requires the battery to pay the
binary-entropy-deficit cost plus any correlation-free-energy increase. -/
theorem thermalBit_correlated_approximate_erasure_landauer_freeEnergy_bound
    (ε : ℚ≥0) (hε : ε ≤ (1 : ℚ≥0) / 2)
    (β : ℝ) (hβ : 0 < β) {battery : GibbsThermalObject}
    (transition : CorrelatedWorkAssistedTransition
      (gibbsThermalBitAt β hβ) (gibbsThermalBitAt β hβ) battery)
    (hInitial : transition.initialSystem = fairEquilibrium)
    (hFinal : transition.finalSystem = approximateErasedBit ε hε) :
    approximateErasureCost β ε +
        transition.correlationFreeEnergyIncrease ≤
      transition.batteryFreeEnergyDecrease := by
  have hbound := transition.landauer_freeEnergy_bound
  unfold CorrelatedWorkAssistedTransition.systemFreeEnergyIncrease at hbound
  rw [hInitial, hFinal, approximateErasedBit_freeEnergyGap ε hε β hβ,
    thermalBitAt_fair_freeEnergyGap β hβ, sub_zero] at hbound
  exact hbound

/-- Entropy-neutral battery form of the correlation-corrected approximate
Boolean Landauer work bound. -/
theorem thermalBit_correlated_approximate_erasure_landauer_work_bound
    (ε : ℚ≥0) (hε : ε ≤ (1 : ℚ≥0) / 2)
    (β : ℝ) (hβ : 0 < β) {battery : GibbsThermalObject}
    (transition : CorrelatedWorkAssistedTransition
      (gibbsThermalBitAt β hβ) (gibbsThermalBitAt β hβ) battery)
    (hInitial : transition.initialSystem = fairEquilibrium)
    (hFinal : transition.finalSystem = approximateErasedBit ε hε)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    approximateErasureCost β ε +
        transition.correlationFreeEnergyIncrease ≤
      transition.batteryEnergyDecrease := by
  have hbound := transition.landauer_work_bound hEntropy
  unfold CorrelatedWorkAssistedTransition.systemFreeEnergyIncrease at hbound
  rw [hInitial, hFinal, approximateErasedBit_freeEnergyGap ε hε β hβ,
    thermalBitAt_fair_freeEnergyGap β hβ, sub_zero] at hbound
  exact hbound

-- Zero, quarter, and half-error targets reduce to the expected exact masses.
#eval decide
  ((approximateErasedBit 0 (by norm_num)).prob false = 1 ∧
    (approximateErasedBit 0 (by norm_num)).prob true = 0 ∧
    (approximateErasedBit ((1 : ℚ≥0) / 4) quarterError_le_half).prob false =
      (3 : ℚ≥0) / 4 ∧
    (approximateErasedBit ((1 : ℚ≥0) / 4) quarterError_le_half).prob true =
      (1 : ℚ≥0) / 4 ∧
    (approximateErasedBit ((1 : ℚ≥0) / 2) (by norm_num)).prob false =
      (1 : ℚ≥0) / 2 ∧
    (approximateErasedBit ((1 : ℚ≥0) / 2) (by norm_num)).prob true =
      (1 : ℚ≥0) / 2)

end Ript.Examples.SimpleThermalModel
