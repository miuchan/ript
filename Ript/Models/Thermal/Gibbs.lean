import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
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

/-- The real coercions of an exact finite distribution's probabilities still
sum to one. -/
theorem finDist_sum_prob_real {X : Object.{u}} (state : FinDist X) :
    ∑ x : X, (state.prob x : ℝ) = 1 := by
  rw [← NNRat.cast_sum, state.normalized]
  exact NNRat.cast_one

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

/-- Canonical Gibbs data realizing a full-support exact equilibrium at a
chosen positive inverse temperature.  The energy gauge is fixed by taking the
partition function to be one: `E(x) = -log γ(x) / β`. -/
def ofFullSupport (thermal : ThermalObject.{u}) (β : ℝ) (hβ : 0 < β)
    (_hfull : ∀ x, thermal.equilibrium.prob x ≠ 0) :
    FiniteGibbsData thermal.system where
  energy x := -Real.log (thermal.equilibrium.prob x : ℝ) / β
  inverseTemperature := β
  inverseTemperature_pos := hβ
  nonempty := thermal.equilibrium.carrier_nonempty

/-- Unnormalized Boltzmann weight `exp (-β E(x))`. -/
def weight {X : Object.{u}} (data : FiniteGibbsData X) (x : X) : ℝ :=
  Real.exp (-data.inverseTemperature * data.energy x)

/-- Finite partition function `Z = sum_x exp (-β E(x))`. -/
def partitionFunction {X : Object.{u}} (data : FiniteGibbsData X) : ℝ :=
  ∑ x : X, data.weight x

/-- Normalized real Gibbs probability. -/
def probability {X : Object.{u}} (data : FiniteGibbsData X) (x : X) : ℝ :=
  data.weight x / data.partitionFunction

/-- The canonical energy assignment recovers the exact equilibrium mass as
its unnormalized Boltzmann weight. -/
theorem ofFullSupport_weight (thermal : ThermalObject.{u}) (β : ℝ)
    (hβ : 0 < β) (hfull : ∀ x, thermal.equilibrium.prob x ≠ 0)
    (x : thermal.system) :
    (ofFullSupport thermal β hβ hfull).weight x =
      (thermal.equilibrium.prob x : ℝ) := by
  have hprob_pos : 0 < (thermal.equilibrium.prob x : ℝ) :=
    NNRat.cast_pos.mpr (pos_iff_ne_zero.mpr (hfull x))
  unfold weight ofFullSupport
  rw [show -β * (-Real.log (thermal.equilibrium.prob x : ℝ) / β) =
      Real.log (thermal.equilibrium.prob x : ℝ) by
    field_simp [ne_of_gt hβ]]
  exact Real.exp_log hprob_pos

/-- The canonical full-support realization uses the normalized gauge `Z = 1`. -/
theorem ofFullSupport_partitionFunction (thermal : ThermalObject.{u}) (β : ℝ)
    (hβ : 0 < β) (hfull : ∀ x, thermal.equilibrium.prob x ≠ 0) :
    (ofFullSupport thermal β hβ hfull).partitionFunction = 1 := by
  classical
  rw [partitionFunction]
  simp_rw [ofFullSupport_weight thermal β hβ hfull]
  exact finDist_sum_prob_real thermal.equilibrium

/-- The normalized Gibbs probability of the canonical realization is exactly
the original full-support equilibrium probability. -/
theorem ofFullSupport_probability (thermal : ThermalObject.{u}) (β : ℝ)
    (hβ : 0 < β) (hfull : ∀ x, thermal.equilibrium.prob x ≠ 0)
    (x : thermal.system) :
    (ofFullSupport thermal β hβ hfull).probability x =
      (thermal.equilibrium.prob x : ℝ) := by
  rw [probability, ofFullSupport_weight thermal β hβ hfull,
    ofFullSupport_partitionFunction thermal β hβ hfull, div_one]

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

/-- Additive energy data for two independent systems at a common inverse
temperature. -/
def tensor {X Y : Object.{u}} (left : FiniteGibbsData X)
    (right : FiniteGibbsData Y)
    (_hTemperature : left.inverseTemperature = right.inverseTemperature) :
    FiniteGibbsData (Object.tensor X Y) where
  energy outcome := left.energy outcome.1 + right.energy outcome.2
  inverseTemperature := left.inverseTemperature
  inverseTemperature_pos := left.inverseTemperature_pos
  nonempty := by
    rcases left.nonempty with ⟨x⟩
    rcases right.nonempty with ⟨y⟩
    exact ⟨(x, y)⟩

/-- Boltzmann weights factor across independent common-temperature systems. -/
theorem tensor_weight {X Y : Object.{u}} (left : FiniteGibbsData X)
    (right : FiniteGibbsData Y)
    (hTemperature : left.inverseTemperature = right.inverseTemperature)
    (outcome : X × Y) :
    (tensor left right hTemperature).weight outcome =
      left.weight outcome.1 * right.weight outcome.2 := by
  unfold weight tensor
  rw [← Real.exp_add]
  congr 1
  rw [← hTemperature]
  ring

/-- Partition functions multiply across independent common-temperature
systems. -/
theorem tensor_partitionFunction {X Y : Object.{u}}
    (left : FiniteGibbsData X) (right : FiniteGibbsData Y)
    (hTemperature : left.inverseTemperature = right.inverseTemperature) :
    (tensor left right hTemperature).partitionFunction =
      left.partitionFunction * right.partitionFunction := by
  classical
  rw [partitionFunction]
  simp_rw [tensor_weight left right hTemperature]
  rw [Fintype.sum_prod_type]
  change (∑ x : X, ∑ y : Y, left.weight x * right.weight y) =
    (∑ x : X, left.weight x) * ∑ y : Y, right.weight y
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Gibbs probabilities factor across independent common-temperature
systems. -/
theorem tensor_probability {X Y : Object.{u}} (left : FiniteGibbsData X)
    (right : FiniteGibbsData Y)
    (hTemperature : left.inverseTemperature = right.inverseTemperature)
    (outcome : X × Y) :
    (tensor left right hTemperature).probability outcome =
      left.probability outcome.1 * right.probability outcome.2 := by
  rw [probability, tensor_weight left right hTemperature,
    tensor_partitionFunction left right hTemperature]
  exact mul_div_mul_comm (left.weight outcome.1) (right.weight outcome.2)
    left.partitionFunction right.partitionFunction

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

/-- Package any full-support exact equilibrium as a canonical finite Gibbs
realization at the chosen positive inverse temperature. -/
def ofFullSupport (thermal : ThermalObject.{u}) (β : ℝ) (hβ : 0 < β)
    (hfull : ∀ x, thermal.equilibrium.prob x ≠ 0) :
    GibbsThermalObject.{u} where
  thermal := thermal
  gibbs := FiniteGibbsData.ofFullSupport thermal β hβ hfull
  equilibrium_eq_probability x :=
    (FiniteGibbsData.ofFullSupport_probability thermal β hβ hfull x).symm

/-- Independent composition of two exact Gibbs realizations at the same
inverse temperature. -/
def tensor (left right : GibbsThermalObject.{u})
    (hTemperature : left.gibbs.inverseTemperature =
      right.gibbs.inverseTemperature) : GibbsThermalObject.{u} where
  thermal :=
    { system := Object.tensor left.thermal.system right.thermal.system
      equilibrium := left.thermal.equilibrium.tensor right.thermal.equilibrium }
  gibbs := left.gibbs.tensor right.gibbs hTemperature
  equilibrium_eq_probability outcome := by
    change left.thermal.system × right.thermal.system at outcome
    change (((left.thermal.equilibrium.tensor right.thermal.equilibrium).prob
      outcome : ℚ≥0) : ℝ) =
      (left.gibbs.tensor right.gibbs hTemperature).probability outcome
    rw [FinDist.tensor_apply, NNRat.cast_mul,
      left.equilibrium_eq_probability outcome.1,
      right.equilibrium_eq_probability outcome.2,
      FiniteGibbsData.tensor_probability left.gibbs right.gibbs hTemperature]

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
