import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Ript.Models.Thermal.Equilibrium

/-!
# Finite Gibbs distributions

This module adds the analytic data that the operational thermal layer
deliberately leaves unspecified.  Energies and inverse temperature are real,
while the executable equilibrium state remains an exact nonnegative-rational
distribution.  `GibbsThermalObject` is therefore a realization certificate:
it says that the exact equilibrium probabilities agree, after coercion to
`ℝ`, with the corresponding normalized Boltzmann weights.

The separation is intentional.  Generic exponential weights need not be
rational, so they cannot honestly be stored in `FinDist`; realizable finite
models retain exact execution without weakening the analytic Gibbs equations.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

noncomputable section

/-- Real energy levels and a strictly positive inverse temperature on a
nonempty executable finite state space. -/
structure FiniteGibbsData (X : Object.{u}) where
  /-- Energy assigned to each microstate. -/
  energy : X → ℝ
  /-- Inverse temperature `β`. -/
  inverseTemperature : ℝ
  /-- Physical inverse temperature is strictly positive. -/
  inverseTemperature_pos : 0 < inverseTemperature
  /-- A normalized finite distribution cannot live on an empty carrier; the
  analytic layer records the witness explicitly for positivity proofs. -/
  nonempty : Nonempty X

namespace FiniteGibbsData

/-- Unnormalized Boltzmann weight `exp (-β E(x))`. -/
def weight {X : Object.{u}} (data : FiniteGibbsData X) (x : X) : ℝ :=
  Real.exp (-data.inverseTemperature * data.energy x)

/-- Finite partition function `Z = sum_x exp (-β E(x))`. -/
def partitionFunction {X : Object.{u}} (data : FiniteGibbsData X) : ℝ :=
  ∑ x : X, data.weight x

/-- Normalized real Gibbs probability. -/
def probability {X : Object.{u}} (data : FiniteGibbsData X) (x : X) : ℝ :=
  data.weight x / data.partitionFunction

/-- Every Boltzmann weight is strictly positive. -/
theorem weight_pos {X : Object.{u}} (data : FiniteGibbsData X) (x : X) :
    0 < data.weight x := by
  exact Real.exp_pos _

/-- The partition function of a nonempty finite Gibbs system is positive. -/
theorem partitionFunction_pos {X : Object.{u}} (data : FiniteGibbsData X) :
    0 < data.partitionFunction := by
  classical
  rw [partitionFunction]
  apply Finset.sum_pos'
  · intro x _
    exact (data.weight_pos x).le
  · exact ⟨Classical.choice data.nonempty, Finset.mem_univ _, data.weight_pos _⟩

/-- In particular, the partition function is nonzero. -/
theorem partitionFunction_ne_zero {X : Object.{u}} (data : FiniteGibbsData X) :
    data.partitionFunction ≠ 0 :=
  ne_of_gt data.partitionFunction_pos

/-- Every normalized Gibbs probability is strictly positive. -/
theorem probability_pos {X : Object.{u}} (data : FiniteGibbsData X) (x : X) :
    0 < data.probability x := by
  exact div_pos (data.weight_pos x) data.partitionFunction_pos

/-- Normalized Gibbs probabilities sum to one. -/
theorem sum_probability {X : Object.{u}} (data : FiniteGibbsData X) :
    ∑ x : X, data.probability x = 1 := by
  simp only [probability, div_eq_mul_inv, ← Finset.sum_mul]
  change data.partitionFunction * data.partitionFunction⁻¹ = 1
  rw [mul_inv_cancel₀ data.partitionFunction_ne_zero]

/-- Logarithm of a normalized Gibbs probability. -/
theorem log_probability {X : Object.{u}} (data : FiniteGibbsData X) (x : X) :
    Real.log (data.probability x) =
      -data.inverseTemperature * data.energy x -
        Real.log data.partitionFunction := by
  rw [probability, Real.log_div (ne_of_gt (data.weight_pos x))
    data.partitionFunction_ne_zero, weight, Real.log_exp]

end FiniteGibbsData

/-- A finite operational thermal object whose exact rational equilibrium
realizes an analytic Gibbs distribution. -/
structure GibbsThermalObject where
  /-- Underlying exact finite thermal object. -/
  thermal : ThermalObject.{u}
  /-- Energy levels and inverse temperature. -/
  gibbs : FiniteGibbsData thermal.system
  /-- Exact equilibrium masses agree with normalized Boltzmann weights after
  coercion to the reals. -/
  equilibrium_eq_probability : ∀ x,
    (thermal.equilibrium.prob x : ℝ) = gibbs.probability x

namespace GibbsThermalObject

/-- A realized Gibbs equilibrium has full support in the exact rational
representation. -/
theorem equilibrium_fullSupport (X : GibbsThermalObject.{u}) :
    ∀ x, X.thermal.equilibrium.prob x ≠ 0 := by
  intro x hx
  have hpos : 0 < (X.thermal.equilibrium.prob x : ℝ) := by
    rw [X.equilibrium_eq_probability x]
    exact X.gibbs.probability_pos x
  rw [hx] at hpos
  exact (lt_irrefl (0 : ℝ)) (by simpa only [NNRat.cast_zero] using hpos)

end GibbsThermalObject

end

end Ript.Models.Thermal
