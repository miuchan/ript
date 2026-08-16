import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.NNRat.BigOperators
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

/-- The real probabilities of an exact finite distribution sum to one. -/
theorem FinDist.sum_prob_real {X : Object.{u}} (state : FinDist X) :
    ∑ x : X, (state.prob x : ℝ) = 1 := by
  rw [← NNRat.cast_sum, state.normalized]
  exact NNRat.cast_one

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
      rw [FinDist.sum_prob_real state]
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
