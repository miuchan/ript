import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Ript.Models.Thermal.Gibbs
import Ript.Models.Thermal.KLDivergence

/-!
# Free energy from finite KL divergence

For a finite Gibbs realization this module defines mean energy, Shannon
entropy, nonequilibrium Helmholtz free energy, and the equilibrium free
energy.  Its main identity is the exact finite formula

`D(p || γ) = β (F(p) - F(γ))`,

where the left side is Ript's measure-theoretic KL divergence converted to a
real number.  The equilibrium realization has full support, so this conversion
never discards an infinite value.

Combining the identity with the already proved stochastic data-processing
theorem yields monotonicity of the free-energy gap under Gibbs-preserving
channels at common inverse temperature.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open scoped ENNReal
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Probability.FiniteKL

universe u

noncomputable section

namespace GibbsThermalObject

/-- Mean energy of an exact state in a finite Gibbs realization. -/
def meanEnergy (X : GibbsThermalObject.{u})
    (state : FinDist X.thermal.system) : ℝ :=
  ∑ x : X.thermal.system,
    (state.prob x : ℝ) * X.gibbs.energy x

/-- Shannon entropy `-sum_x p(x) log p(x)`, with Lean's `log 0 = 0`
realizing the usual zero-mass convention. -/
def entropy (X : GibbsThermalObject.{u})
    (state : FinDist X.thermal.system) : ℝ :=
  -∑ x : X.thermal.system,
    (state.prob x : ℝ) * Real.log (state.prob x : ℝ)

/-- Nonequilibrium Helmholtz free energy `E - β⁻¹ S`. -/
def nonequilibriumFreeEnergy (X : GibbsThermalObject.{u})
    (state : FinDist X.thermal.system) : ℝ :=
  X.meanEnergy state - X.entropy state / X.gibbs.inverseTemperature

/-- Equilibrium Helmholtz free energy `-β⁻¹ log Z`. -/
def equilibriumFreeEnergy (X : GibbsThermalObject.{u}) : ℝ :=
  -Real.log X.gibbs.partitionFunction / X.gibbs.inverseTemperature

/-- Excess free energy above the Gibbs equilibrium value. -/
def freeEnergyGap (X : GibbsThermalObject.{u})
    (state : FinDist X.thermal.system) : ℝ :=
  X.nonequilibriumFreeEnergy state - X.equilibriumFreeEnergy

/-- Mean energy is additive for independent states of common-temperature
Gibbs systems. -/
theorem meanEnergy_tensor (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (p : FinDist left.thermal.system) (q : FinDist right.thermal.system) :
    (left.tensor right hTemperature).meanEnergy (p.tensor q) =
      left.meanEnergy p + right.meanEnergy q := by
  classical
  change (∑ outcome : left.thermal.system × right.thermal.system,
      ((p.prob outcome.1 * q.prob outcome.2 : ℚ≥0) : ℝ) *
        (left.gibbs.energy outcome.1 + right.gibbs.energy outcome.2)) =
    (∑ x : left.thermal.system,
      (p.prob x : ℝ) * left.gibbs.energy x) +
    ∑ y : right.thermal.system,
      (q.prob y : ℝ) * right.gibbs.energy y
  simp_rw [NNRat.cast_mul]
  have hleft :
      (∑ outcome : left.thermal.system × right.thermal.system,
        (p.prob outcome.1 : ℝ) * (q.prob outcome.2 : ℝ) *
          left.gibbs.energy outcome.1) =
        (∑ x : left.thermal.system,
          (p.prob x : ℝ) * left.gibbs.energy x) *
        ∑ y : right.thermal.system, (q.prob y : ℝ) := by
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
    apply Fintype.sum_congr
    intro x
    apply Fintype.sum_congr
    intro y
    ring
  have hright :
      (∑ outcome : left.thermal.system × right.thermal.system,
        (p.prob outcome.1 : ℝ) * (q.prob outcome.2 : ℝ) *
          right.gibbs.energy outcome.2) =
        (∑ x : left.thermal.system, (p.prob x : ℝ)) *
        ∑ y : right.thermal.system,
          (q.prob y : ℝ) * right.gibbs.energy y := by
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
    apply Fintype.sum_congr
    intro x
    apply Fintype.sum_congr
    intro y
    ring
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hleft, hright,
    finDist_sum_prob_real p, finDist_sum_prob_real q]
  ring

/-- Pointwise logarithmic identity underlying Shannon-entropy additivity,
including the zero-mass boundary cases. -/
theorem entropy_tensor_term (a b : ℚ≥0) :
    (((a * b : ℚ≥0) : ℝ) * Real.log ((a * b : ℚ≥0) : ℝ)) =
      (b : ℝ) * ((a : ℝ) * Real.log (a : ℝ)) +
      (a : ℝ) * ((b : ℝ) * Real.log (b : ℝ)) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha_real : (a : ℝ) ≠ 0 := by simpa using ha
  have hb_real : (b : ℝ) ≠ 0 := by simpa using hb
  rw [NNRat.cast_mul, Real.log_mul ha_real hb_real]
  ring

/-- Shannon entropy is additive on independent product states. -/
theorem entropy_tensor (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (p : FinDist left.thermal.system) (q : FinDist right.thermal.system) :
    (left.tensor right hTemperature).entropy (p.tensor q) =
      left.entropy p + right.entropy q := by
  classical
  change -(∑ outcome : left.thermal.system × right.thermal.system,
      (((p.prob outcome.1 * q.prob outcome.2 : ℚ≥0) : ℝ) *
        Real.log ((p.prob outcome.1 * q.prob outcome.2 : ℚ≥0) : ℝ))) =
    -(∑ x : left.thermal.system,
      (p.prob x : ℝ) * Real.log (p.prob x : ℝ)) +
    -(∑ y : right.thermal.system,
      (q.prob y : ℝ) * Real.log (q.prob y : ℝ))
  simp_rw [entropy_tensor_term]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  have hleft :
      (∑ x : left.thermal.system, ∑ y : right.thermal.system,
        (q.prob y : ℝ) *
          ((p.prob x : ℝ) * Real.log (p.prob x : ℝ))) =
        (∑ x : left.thermal.system,
          (p.prob x : ℝ) * Real.log (p.prob x : ℝ)) *
        ∑ y : right.thermal.system, (q.prob y : ℝ) := by
    rw [Fintype.sum_mul_sum]
    apply Fintype.sum_congr
    intro x
    apply Fintype.sum_congr
    intro y
    ring
  have hright :
      (∑ x : left.thermal.system, ∑ y : right.thermal.system,
        (p.prob x : ℝ) *
          ((q.prob y : ℝ) * Real.log (q.prob y : ℝ))) =
        (∑ x : left.thermal.system, (p.prob x : ℝ)) *
        ∑ y : right.thermal.system,
          (q.prob y : ℝ) * Real.log (q.prob y : ℝ) := by
    rw [Fintype.sum_mul_sum]
  rw [hleft, hright,
    finDist_sum_prob_real p, finDist_sum_prob_real q]
  ring

/-- Equilibrium Helmholtz free energy is additive for independent
common-temperature Gibbs systems. -/
theorem equilibriumFreeEnergy_tensor (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature) :
    (left.tensor right hTemperature).equilibriumFreeEnergy =
      left.equilibriumFreeEnergy + right.equilibriumFreeEnergy := by
  change -Real.log
        (left.gibbs.tensor right.gibbs hTemperature).partitionFunction /
      left.gibbs.inverseTemperature =
    -Real.log left.gibbs.partitionFunction /
        left.gibbs.inverseTemperature +
      -Real.log right.gibbs.partitionFunction /
        right.gibbs.inverseTemperature
  rw [FiniteGibbsData.tensor_partitionFunction left.gibbs right.gibbs
      hTemperature,
    Real.log_mul left.gibbs.partitionFunction_ne_zero
      right.gibbs.partitionFunction_ne_zero]
  rw [← hTemperature]
  field_simp [ne_of_gt left.gibbs.inverseTemperature_pos]
  ring

/-- Nonequilibrium Helmholtz free energy is additive on independent states of
common-temperature Gibbs systems. -/
theorem nonequilibriumFreeEnergy_tensor
    (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (p : FinDist left.thermal.system) (q : FinDist right.thermal.system) :
    (left.tensor right hTemperature).nonequilibriumFreeEnergy (p.tensor q) =
      left.nonequilibriumFreeEnergy p + right.nonequilibriumFreeEnergy q := by
  unfold nonequilibriumFreeEnergy
  rw [meanEnergy_tensor left right hTemperature p q,
    entropy_tensor left right hTemperature p q]
  change left.meanEnergy p + right.meanEnergy q -
      (left.entropy p + right.entropy q) /
        left.gibbs.inverseTemperature =
    (left.meanEnergy p -
      left.entropy p / left.gibbs.inverseTemperature) +
    (right.meanEnergy q -
      right.entropy q / right.gibbs.inverseTemperature)
  rw [← hTemperature]
  field_simp [ne_of_gt left.gibbs.inverseTemperature_pos]
  ring

/-- Excess free energy is additive on independent states of
common-temperature Gibbs systems. -/
theorem freeEnergyGap_tensor (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature)
    (p : FinDist left.thermal.system) (q : FinDist right.thermal.system) :
    (left.tensor right hTemperature).freeEnergyGap (p.tensor q) =
      left.freeEnergyGap p + right.freeEnergyGap q := by
  unfold freeEnergyGap
  rw [nonequilibriumFreeEnergy_tensor left right hTemperature p q,
    equilibriumFreeEnergy_tensor left right hTemperature]
  ring

/-- The pointwise classical KL summand expands into entropy, energy, and
partition-function contributions. -/
theorem finiteKLRealTerm_eq_entropy_energy_partition
    (X : GibbsThermalObject.{u}) (state : FinDist X.thermal.system)
    (x : X.thermal.system) :
    finiteKLRealTerm state X.thermal.equilibrium x =
      (state.prob x : ℝ) * Real.log (state.prob x : ℝ) +
      X.gibbs.inverseTemperature *
        ((state.prob x : ℝ) * X.gibbs.energy x) +
      (state.prob x : ℝ) * Real.log X.gibbs.partitionFunction := by
  by_cases hp : state.prob x = 0
  · simp [finiteKLRealTerm, hp]
  · have hp_real : (state.prob x : ℝ) ≠ 0 := by
      intro hcast
      apply hp
      apply NNRat.cast_injective (α := ℝ)
      simpa only [NNRat.cast_zero] using hcast
    rw [finiteKLRealTerm, X.equilibrium_eq_probability x,
      Real.log_div hp_real (ne_of_gt (X.gibbs.probability_pos x)),
      X.gibbs.log_probability x]
    ring

/-- The explicit finite KL sum is `β E(p) - S(p) + log Z`. -/
theorem sum_finiteKLRealTerm_eq
    (X : GibbsThermalObject.{u}) (state : FinDist X.thermal.system) :
    (∑ x : X.thermal.system,
      finiteKLRealTerm state X.thermal.equilibrium x) =
      -X.entropy state +
        X.gibbs.inverseTemperature * X.meanEnergy state +
        Real.log X.gibbs.partitionFunction := by
  classical
  calc
    (∑ x : X.thermal.system,
        finiteKLRealTerm state X.thermal.equilibrium x) =
        ∑ x : X.thermal.system,
          ((state.prob x : ℝ) * Real.log (state.prob x : ℝ) +
            X.gibbs.inverseTemperature *
              ((state.prob x : ℝ) * X.gibbs.energy x) +
            (state.prob x : ℝ) * Real.log X.gibbs.partitionFunction) := by
      apply Finset.sum_congr rfl
      intro x _
      exact X.finiteKLRealTerm_eq_entropy_energy_partition state x
    _ = (∑ x : X.thermal.system,
          (state.prob x : ℝ) * Real.log (state.prob x : ℝ)) +
        X.gibbs.inverseTemperature *
          (∑ x : X.thermal.system,
            (state.prob x : ℝ) * X.gibbs.energy x) +
        (∑ x : X.thermal.system, (state.prob x : ℝ)) *
          Real.log X.gibbs.partitionFunction := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_mul]
    _ = -X.entropy state +
        X.gibbs.inverseTemperature * X.meanEnergy state +
        Real.log X.gibbs.partitionFunction := by
      rw [finDist_sum_prob_real state]
      simp [entropy, meanEnergy]

/-- KL athermality of a realized Gibbs state is always finite. -/
theorem klAthermality_ne_top (X : GibbsThermalObject.{u})
    (state : FinDist X.thermal.system) :
    klAthermality X.thermal state ≠ ∞ := by
  change finiteKL state X.thermal.equilibrium ≠ ∞
  apply finiteKL_ne_top_of_absolutelyContinuous
  rw [distributionMeasure_absolutelyContinuous_iff]
  intro x hzero
  exact False.elim (X.equilibrium_fullSupport x hzero)

/-- **KL/free-energy identity.** For every exact state in a realized finite
Gibbs system, KL divergence from equilibrium is inverse temperature times its
nonequilibrium free-energy excess. -/
theorem klAthermality_toReal_eq_inverseTemperature_mul_freeEnergyGap
    (X : GibbsThermalObject.{u}) (state : FinDist X.thermal.system) :
    (klAthermality X.thermal state).toReal =
      X.gibbs.inverseTemperature * X.freeEnergyGap state := by
  rw [klAthermality_eq,
    finiteKL_toReal_eq_sum_of_fullSupport X.equilibrium_fullSupport,
    X.sum_finiteKLRealTerm_eq state]
  unfold freeEnergyGap nonequilibriumFreeEnergy equilibriumFreeEnergy
  field_simp [ne_of_gt X.gibbs.inverseTemperature_pos]
  ring

/-- The distinguished Gibbs equilibrium has zero excess free energy. -/
@[simp]
theorem freeEnergyGap_equilibrium (X : GibbsThermalObject.{u}) :
    X.freeEnergyGap X.thermal.equilibrium = 0 := by
  have hidentity :=
    X.klAthermality_toReal_eq_inverseTemperature_mul_freeEnergyGap
      X.thermal.equilibrium
  rw [klAthermality_eq, finiteKL_self] at hidentity
  have hmul : X.gibbs.inverseTemperature *
      X.freeEnergyGap X.thermal.equilibrium = 0 := by
    simpa using hidentity.symm
  exact (mul_eq_zero.mp hmul).resolve_left
    (ne_of_gt X.gibbs.inverseTemperature_pos)

/-- **Free-energy gap monotonicity.** A Gibbs-preserving channel between
realized systems at the same inverse temperature cannot increase excess free
energy. -/
theorem freeEnergyGap_monotone {X Y : GibbsThermalObject.{u}}
    (hTemperature : Y.gibbs.inverseTemperature =
      X.gibbs.inverseTemperature)
    (process : GibbsPreserving X.thermal Y.thermal)
    (state : FinDist X.thermal.system) :
    Y.freeEnergyGap (state.push process.channel) ≤ X.freeEnergyGap state := by
  have hkl := klAthermality_monotone process state
  have hreal :
      (klAthermality Y.thermal (state.push process.channel)).toReal ≤
        (klAthermality X.thermal state).toReal :=
    ENNReal.toReal_mono (X.klAthermality_ne_top state) hkl
  rw [Y.klAthermality_toReal_eq_inverseTemperature_mul_freeEnergyGap,
    X.klAthermality_toReal_eq_inverseTemperature_mul_freeEnergyGap,
    hTemperature] at hreal
  exact le_of_mul_le_mul_left hreal X.gibbs.inverseTemperature_pos

end GibbsThermalObject

end

end Ript.Models.Thermal
