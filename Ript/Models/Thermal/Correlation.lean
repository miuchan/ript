import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Ript.Models.Thermal.FreeEnergy

/-!
# Correlation free energy for finite Gibbs systems

This module extends the independent tensor laws to arbitrary exact joint
states.  The left and right marginal distributions remain executable rational
data.  Their Shannon mutual information is the entropy deficit of the joint
state relative to its marginals, and the corresponding correlation free
energy is that deficit divided by the common inverse temperature.

For an arbitrary joint state `p`, not assumed to factor, the total excess
Helmholtz free energy decomposes exactly into the two marginal free-energy
gaps plus correlation free energy.  Independent products are recovered as the
zero-correlation special case.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open MeasureTheory
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Probability.FiniteKL

universe u

noncomputable section

/-- A joint distribution is absolutely continuous with respect to the
independent product of its marginals. -/
theorem joint_absolutelyContinuous_tensor_marginals
    {X Y : Object.{u}} (joint : FinDist (Object.tensor X Y)) :
    distributionMeasure joint ≪
      distributionMeasure
        (joint.leftMarginal.tensor joint.rightMarginal) := by
  rw [distributionMeasure_absolutelyContinuous_iff]
  exact FinDist.support_tensor_marginals joint

/-- Pointwise logarithmic expansion of joint KL relative to the product of
the marginals, including zero-mass boundary cases. -/
theorem finiteKLRealTerm_tensor_marginals
    {X Y : Object.{u}} (joint : FinDist (Object.tensor X Y))
    (outcome : X × Y) :
    finiteKLRealTerm joint
        (joint.leftMarginal.tensor joint.rightMarginal) outcome =
      (joint.prob outcome : ℝ) * Real.log (joint.prob outcome : ℝ) -
        (joint.prob outcome : ℝ) *
          Real.log (joint.leftMarginal.prob outcome.1 : ℝ) -
        (joint.prob outcome : ℝ) *
          Real.log (joint.rightMarginal.prob outcome.2 : ℝ) := by
  by_cases hjoint : joint.prob outcome = 0
  · simp [finiteKLRealTerm, hjoint]
  have hleft : joint.leftMarginal.prob outcome.1 ≠ 0 := by
    intro hzero
    exact hjoint (FinDist.joint_prob_eq_zero_of_leftMarginal_eq_zero
      joint outcome.1 outcome.2 hzero)
  have hright : joint.rightMarginal.prob outcome.2 ≠ 0 := by
    intro hzero
    exact hjoint (FinDist.joint_prob_eq_zero_of_rightMarginal_eq_zero
      joint outcome.1 outcome.2 hzero)
  have hjointReal : (joint.prob outcome : ℝ) ≠ 0 := by
    intro hzero
    apply hjoint
    apply NNRat.cast_injective (α := ℝ)
    simpa using hzero
  have hleftReal : (joint.leftMarginal.prob outcome.1 : ℝ) ≠ 0 := by
    intro hzero
    apply hleft
    apply NNRat.cast_injective (α := ℝ)
    simpa using hzero
  have hrightReal : (joint.rightMarginal.prob outcome.2 : ℝ) ≠ 0 := by
    intro hzero
    apply hright
    apply NNRat.cast_injective (α := ℝ)
    simpa using hzero
  rw [finiteKLRealTerm, FinDist.tensor_apply, NNRat.cast_mul,
    Real.log_div hjointReal (mul_ne_zero hleftReal hrightReal),
    Real.log_mul hleftReal hrightReal]
  ring

/-- Summing a joint mass against a function of the left coordinate is the
same as taking the expectation under the left marginal, specialized to the
logarithmic entropy term. -/
theorem sum_joint_mul_log_leftMarginal
    {X Y : Object.{u}} (joint : FinDist (Object.tensor X Y)) :
    (∑ outcome : X × Y,
      (joint.prob outcome : ℝ) *
        Real.log (joint.leftMarginal.prob outcome.1 : ℝ)) =
      ∑ x : X, (joint.leftMarginal.prob x : ℝ) *
        Real.log (joint.leftMarginal.prob x : ℝ) := by
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro x
  change (∑ y : Y, (joint.prob (x, y) : ℝ) *
      Real.log (joint.leftMarginal.prob x : ℝ)) =
    (joint.leftMarginal.prob x : ℝ) *
      Real.log (joint.leftMarginal.prob x : ℝ)
  rw [FinDist.leftMarginal_apply, NNRat.cast_sum, Finset.sum_mul]

/-- Right-coordinate counterpart of
`sum_joint_mul_log_leftMarginal`. -/
theorem sum_joint_mul_log_rightMarginal
    {X Y : Object.{u}} (joint : FinDist (Object.tensor X Y)) :
    (∑ outcome : X × Y,
      (joint.prob outcome : ℝ) *
        Real.log (joint.rightMarginal.prob outcome.2 : ℝ)) =
      ∑ y : Y, (joint.rightMarginal.prob y : ℝ) *
        Real.log (joint.rightMarginal.prob y : ℝ) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Fintype.sum_congr
  intro y
  change (∑ x : X, (joint.prob (x, y) : ℝ) *
      Real.log (joint.rightMarginal.prob y : ℝ)) =
    (joint.rightMarginal.prob y : ℝ) *
      Real.log (joint.rightMarginal.prob y : ℝ)
  rw [FinDist.rightMarginal_apply, NNRat.cast_sum, Finset.sum_mul]

/-- Joint KL relative to the independent product of the marginals is the
corresponding entropy-deficit finite sum. -/
theorem finiteKL_toReal_tensor_marginals_eq_entropy_deficit
    {X Y : Object.{u}} (joint : FinDist (Object.tensor X Y)) :
    (finiteKL joint
      (joint.leftMarginal.tensor joint.rightMarginal)).toReal =
      (∑ outcome : X × Y,
        (joint.prob outcome : ℝ) * Real.log (joint.prob outcome : ℝ)) -
      (∑ x : X, (joint.leftMarginal.prob x : ℝ) *
        Real.log (joint.leftMarginal.prob x : ℝ)) -
      ∑ y : Y, (joint.rightMarginal.prob y : ℝ) *
        Real.log (joint.rightMarginal.prob y : ℝ) := by
  rw [finiteKL_toReal_eq_sum_of_absolutelyContinuous
    (joint_absolutelyContinuous_tensor_marginals joint)]
  calc
    (∑ outcome : X × Y,
        finiteKLRealTerm joint
          (joint.leftMarginal.tensor joint.rightMarginal) outcome) =
        ∑ outcome : X × Y,
          ((joint.prob outcome : ℝ) * Real.log (joint.prob outcome : ℝ) -
            (joint.prob outcome : ℝ) *
              Real.log (joint.leftMarginal.prob outcome.1 : ℝ) -
            (joint.prob outcome : ℝ) *
              Real.log (joint.rightMarginal.prob outcome.2 : ℝ)) := by
      apply Fintype.sum_congr
      intro outcome
      exact finiteKLRealTerm_tensor_marginals joint outcome
    _ = (∑ outcome : X × Y,
          (joint.prob outcome : ℝ) * Real.log (joint.prob outcome : ℝ)) -
        (∑ outcome : X × Y,
          (joint.prob outcome : ℝ) *
            Real.log (joint.leftMarginal.prob outcome.1 : ℝ)) -
        ∑ outcome : X × Y,
          (joint.prob outcome : ℝ) *
            Real.log (joint.rightMarginal.prob outcome.2 : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      rw [sum_joint_mul_log_leftMarginal joint,
        sum_joint_mul_log_rightMarginal joint]

namespace GibbsThermalObject

/-- Shannon mutual information of an exact joint state, expressed as the
entropy deficit relative to its two marginals. -/
def mutualInformation (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) : ℝ :=
  left.entropy joint.leftMarginal + right.entropy joint.rightMarginal -
    (left.tensor right hTemperature).entropy joint

/-- Free energy stored in correlations at a common inverse temperature. -/
def correlationFreeEnergy (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) : ℝ :=
  left.mutualInformation right hTemperature joint /
    left.gibbs.inverseTemperature

/-- Shannon mutual information is exactly finite KL divergence from the joint
state to the independent product of its marginals. -/
theorem mutualInformation_eq_finiteKL_toReal
    (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) :
    left.mutualInformation right hTemperature joint =
      (finiteKL joint
        (joint.leftMarginal.tensor joint.rightMarginal)).toReal := by
  rw [finiteKL_toReal_tensor_marginals_eq_entropy_deficit]
  unfold mutualInformation entropy
  change
    -(∑ x : left.thermal.system,
        (joint.leftMarginal.prob x : ℝ) *
          Real.log (joint.leftMarginal.prob x : ℝ)) +
      -(∑ y : right.thermal.system,
        (joint.rightMarginal.prob y : ℝ) *
          Real.log (joint.rightMarginal.prob y : ℝ)) -
      -(∑ outcome : left.thermal.system × right.thermal.system,
        (joint.prob outcome : ℝ) * Real.log (joint.prob outcome : ℝ)) =
    (∑ outcome : left.thermal.system × right.thermal.system,
      (joint.prob outcome : ℝ) * Real.log (joint.prob outcome : ℝ)) -
      (∑ x : left.thermal.system,
        (joint.leftMarginal.prob x : ℝ) *
          Real.log (joint.leftMarginal.prob x : ℝ)) -
      ∑ y : right.thermal.system,
        (joint.rightMarginal.prob y : ℝ) *
          Real.log (joint.rightMarginal.prob y : ℝ)
  ring

/-- Mutual information of an exact finite joint state is nonnegative. -/
theorem mutualInformation_nonneg (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) :
    0 ≤ left.mutualInformation right hTemperature joint := by
  rw [mutualInformation_eq_finiteKL_toReal]
  exact ENNReal.toReal_nonneg

/-- Correlation free energy is nonnegative at positive inverse temperature. -/
theorem correlationFreeEnergy_nonneg (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) :
    0 ≤ left.correlationFreeEnergy right hTemperature joint := by
  exact div_nonneg
    (left.mutualInformation_nonneg right hTemperature joint)
    left.gibbs.inverseTemperature_pos.le

/-- Mean energy of an arbitrary joint state is the sum of the mean energies
of its marginals for the additive tensor Hamiltonian. -/
theorem meanEnergy_eq_marginals (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) :
    (left.tensor right hTemperature).meanEnergy joint =
      left.meanEnergy joint.leftMarginal +
        right.meanEnergy joint.rightMarginal := by
  classical
  change (∑ outcome : left.thermal.system × right.thermal.system,
      (joint.prob outcome : ℝ) *
        (left.gibbs.energy outcome.1 + right.gibbs.energy outcome.2)) =
    (∑ x : left.thermal.system,
      (joint.leftMarginal.prob x : ℝ) * left.gibbs.energy x) +
    ∑ y : right.thermal.system,
      (joint.rightMarginal.prob y : ℝ) * right.gibbs.energy y
  rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hleft :
      (∑ x : left.thermal.system, ∑ y : right.thermal.system,
        (joint.prob (x, y) : ℝ) * left.gibbs.energy x) =
        ∑ x : left.thermal.system,
          (joint.leftMarginal.prob x : ℝ) * left.gibbs.energy x := by
    apply Fintype.sum_congr
    intro x
    rw [FinDist.leftMarginal_apply, NNRat.cast_sum, Finset.sum_mul]
  have hright :
      (∑ x : left.thermal.system, ∑ y : right.thermal.system,
        (joint.prob (x, y) : ℝ) * right.gibbs.energy y) =
        ∑ y : right.thermal.system,
          (joint.rightMarginal.prob y : ℝ) * right.gibbs.energy y := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro y
    rw [FinDist.rightMarginal_apply, NNRat.cast_sum, Finset.sum_mul]
  rw [hleft, hright]

/-- Nonequilibrium free energy of an arbitrary joint state is the sum of its
marginal free energies and its correlation free energy. -/
theorem nonequilibriumFreeEnergy_eq_marginals_add_correlation
    (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) :
    (left.tensor right hTemperature).nonequilibriumFreeEnergy joint =
      left.nonequilibriumFreeEnergy joint.leftMarginal +
        right.nonequilibriumFreeEnergy joint.rightMarginal +
          left.correlationFreeEnergy right hTemperature joint := by
  unfold nonequilibriumFreeEnergy correlationFreeEnergy mutualInformation
  rw [meanEnergy_eq_marginals left right hTemperature joint]
  change left.meanEnergy joint.leftMarginal +
      right.meanEnergy joint.rightMarginal -
        (left.tensor right hTemperature).entropy joint /
          left.gibbs.inverseTemperature =
    (left.meanEnergy joint.leftMarginal -
      left.entropy joint.leftMarginal /
        left.gibbs.inverseTemperature) +
    (right.meanEnergy joint.rightMarginal -
      right.entropy joint.rightMarginal /
        right.gibbs.inverseTemperature) +
    (left.entropy joint.leftMarginal +
      right.entropy joint.rightMarginal -
        (left.tensor right hTemperature).entropy joint) /
      left.gibbs.inverseTemperature
  rw [← hTemperature]
  field_simp [ne_of_gt left.gibbs.inverseTemperature_pos]
  ring

/-- Excess free energy of an arbitrary joint state decomposes into marginal
excess free energies plus correlation free energy. -/
theorem freeEnergyGap_eq_marginals_add_correlation
    (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (joint : FinDist (Object.tensor left.thermal.system
      right.thermal.system)) :
    (left.tensor right hTemperature).freeEnergyGap joint =
      left.freeEnergyGap joint.leftMarginal +
        right.freeEnergyGap joint.rightMarginal +
          left.correlationFreeEnergy right hTemperature joint := by
  unfold freeEnergyGap
  rw [nonequilibriumFreeEnergy_eq_marginals_add_correlation
      left right hTemperature joint,
    equilibriumFreeEnergy_tensor left right hTemperature]
  ring

/-- Independent product states have zero mutual information. -/
@[simp]
theorem mutualInformation_tensor (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (p : FinDist left.thermal.system) (q : FinDist right.thermal.system) :
    left.mutualInformation right hTemperature (p.tensor q) = 0 := by
  unfold mutualInformation
  rw [FinDist.leftMarginal_tensor, FinDist.rightMarginal_tensor,
    entropy_tensor left right hTemperature p q]
  ring

/-- Independent product states store no correlation free energy. -/
@[simp]
theorem correlationFreeEnergy_tensor (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (p : FinDist left.thermal.system) (q : FinDist right.thermal.system) :
    left.correlationFreeEnergy right hTemperature (p.tensor q) = 0 := by
  simp [correlationFreeEnergy]

end GibbsThermalObject

end

end Ript.Models.Thermal
