import Mathlib.Tactic.NormNum
import Ript.Models.Thermal.FreeEnergy

/-!
# Executable finite thermal example

A Boolean system is equipped with the exact uniform equilibrium distribution.
Deterministic bit flip is Gibbs-preserving because it permutes the two equally
weighted energy levels.  The example executes equilibrium evolution, free
state preparation, tensor equilibrium, and serial composition using exact
nonnegative rational arithmetic.
-/

set_option autoImplicit false

namespace Ript.Examples.SimpleThermalModel

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Probability.FiniteKL
open Ript.Models.Thermal

/-- Executable two-state carrier. -/
def bitSystem : Object :=
  Object.of Bool

/-- Exact uniform equilibrium state of the Boolean system. -/
def fairEquilibrium : FinDist bitSystem where
  prob _ := (1 : ℚ≥0) / 2
  normalized := by
    change (∑ value : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- A finite thermal bit with uniform equilibrium. -/
def thermalBit : ThermalObject where
  system := bitSystem
  equilibrium := fairEquilibrium

/-- Degenerate two-level Hamiltonian at inverse temperature one.  Both energy
levels are zero, so its analytic Gibbs distribution is uniform. -/
noncomputable def uniformGibbsData : FiniteGibbsData bitSystem where
  energy _ := 0
  inverseTemperature := 1
  inverseTemperature_pos := by norm_num
  nonempty := ⟨false⟩

/-- The analytic Gibbs probability of either Boolean state is one half. -/
theorem uniformGibbs_probability (x : bitSystem) :
    uniformGibbsData.probability x = (1 : ℝ) / 2 := by
  change Real.exp (-1 * 0) /
      (∑ _ : Bool, Real.exp (-1 * 0)) = (1 : ℝ) / 2
  rw [Fintype.sum_bool]
  norm_num

/-- The exact rational thermal bit realizes the analytic Gibbs distribution. -/
noncomputable def gibbsThermalBit : GibbsThermalObject where
  thermal := thermalBit
  gibbs := uniformGibbsData
  equilibrium_eq_probability x := by
    change Bool at x
    change (((1 : ℚ≥0) / 2 : ℚ≥0) : ℝ) =
      Real.exp (-1 * 0) / (∑ _ : Bool, Real.exp (-1 * 0))
    rw [Fintype.sum_bool]
    norm_num

/-- The uniform exact equilibrium has full support. -/
theorem fairEquilibrium_fullSupport (x : thermalBit.system) :
    thermalBit.equilibrium.prob x ≠ 0 := by
  change (1 : ℚ≥0) / 2 ≠ 0
  norm_num

/-- The generic full-support construction supplies a second, canonically
gauged Gibbs realization of the same exact thermal bit. -/
noncomputable def canonicalGibbsThermalBit : GibbsThermalObject :=
  GibbsThermalObject.ofFullSupport thermalBit 1 (by norm_num)
    fairEquilibrium_fullSupport

/-- The canonical construction recovers the exact uniform mass directly. -/
theorem canonicalGibbsThermalBit_probability (x : thermalBit.system) :
    canonicalGibbsThermalBit.gibbs.probability x =
      (thermalBit.equilibrium.prob x : ℝ) := by
  exact (canonicalGibbsThermalBit.equilibrium_eq_probability x).symm

/-- Deterministic Boolean flip as an exact stochastic channel. -/
def flipChannel : FinStoch bitSystem bitSystem :=
  FinStoch.dirac Bool.not

/-- Boolean flip preserves the uniform equilibrium distribution. -/
theorem flip_preserves_equilibrium :
    fairEquilibrium.push flipChannel = fairEquilibrium := by
  apply FinDist.ext
  intro output
  change Bool at output
  change (∑ input : Bool,
    (1 : ℚ≥0) / 2 * (if (!input) = output then 1 else 0)) = 1 / 2
  cases output <;> rw [Fintype.sum_bool] <;> norm_num

/-- Boolean flip as a free thermodynamic process. -/
def thermalFlip : GibbsPreserving thermalBit thermalBit where
  channel := flipChannel
  preserves_equilibrium := flip_preserves_equilibrium

/-- Two free flips compose to the thermal identity process. -/
theorem thermalFlip_involutive :
    GibbsPreserving.comp thermalFlip thermalFlip =
      GibbsPreserving.identity thermalBit := by
  apply GibbsPreserving.ext
  apply FinStoch.ext
  intro input output
  change Bool at input output
  change (∑ middle : Bool,
    (if (!input) = middle then (1 : ℚ≥0) else 0) *
      (if (!middle) = output then 1 else 0)) =
    if input = output then 1 else 0
  cases input <;> cases output <;> rw [Fintype.sum_bool] <;> norm_num

/-- The equilibrium state's concrete KL athermality is zero. -/
@[simp]
theorem fairEquilibrium_klAthermality :
    klAthermality thermalBit fairEquilibrium = 0 := by
  change finiteKL fairEquilibrium fairEquilibrium = 0
  exact finiteKL_self fairEquilibrium

/-- The uniform Boolean equilibrium has full support, so every state's KL
athermality admits the classical two-term logarithmic formula. -/
theorem klAthermality_toReal_eq_sum (state : FinDist thermalBit.system) :
    (klAthermality thermalBit state).toReal =
      ∑ x : Bool, finiteKLRealTerm state fairEquilibrium x := by
  change (finiteKL state fairEquilibrium).toReal = _
  apply finiteKL_toReal_eq_sum_of_fullSupport
  intro x
  change (1 : ℚ≥0) / 2 ≠ 0
  norm_num

/-- Reversible equilibrium-preserving bit flip leaves concrete KL athermality
unchanged.  Each inequality comes from the full stochastic KL data-processing
theorem; involutivity supplies the reverse inequality. -/
theorem thermalFlip_klAthermality_invariant
    (state : FinDist thermalBit.system) :
    klAthermality thermalBit (state.push thermalFlip.channel) =
      klAthermality thermalBit state := by
  apply le_antisymm
  · exact klAthermality_monotone thermalFlip state
  · have hroundtrip :
        (state.push thermalFlip.channel).push thermalFlip.channel = state := by
      rw [← FinDist.push_comp]
      change state.push
        (GibbsPreserving.comp thermalFlip thermalFlip).channel = state
      rw [thermalFlip_involutive]
      exact FinDist.push_identity state
    have h := klAthermality_monotone thermalFlip
      (state.push thermalFlip.channel)
    rw [hroundtrip] at h
    exact h

/-- On the zero-energy bit, mean energy vanishes for every exact state. -/
@[simp]
theorem thermalBit_meanEnergy (state : FinDist thermalBit.system) :
    gibbsThermalBit.meanEnergy state = 0 := by
  simp [GibbsThermalObject.meanEnergy, gibbsThermalBit, uniformGibbsData]

/-- The Boolean partition function is two, so its equilibrium free energy at
inverse temperature one is `-log 2`. -/
theorem thermalBit_equilibriumFreeEnergy :
    gibbsThermalBit.equilibriumFreeEnergy = -Real.log 2 := by
  change -Real.log (∑ _ : Bool, Real.exp (-1 * 0)) / 1 = -Real.log 2
  rw [Fintype.sum_bool]
  norm_num

/-- The general KL/free-energy theorem specializes without a scaling factor
because the Boolean model has inverse temperature one. -/
theorem thermalBit_kl_freeEnergy_identity
    (state : FinDist thermalBit.system) :
    (klAthermality thermalBit state).toReal =
      gibbsThermalBit.freeEnergyGap state := by
  simpa [gibbsThermalBit, uniformGibbsData] using
    gibbsThermalBit.klAthermality_toReal_eq_inverseTemperature_mul_freeEnergyGap
      state

/-- Reversible equilibrium-preserving bit flip also leaves the concrete
free-energy gap invariant. -/
theorem thermalFlip_freeEnergyGap_invariant
    (state : FinDist thermalBit.system) :
    gibbsThermalBit.freeEnergyGap (state.push thermalFlip.channel) =
      gibbsThermalBit.freeEnergyGap state := by
  apply le_antisymm
  · exact GibbsThermalObject.freeEnergyGap_monotone
      (X := gibbsThermalBit) (Y := gibbsThermalBit) rfl thermalFlip state
  · have hroundtrip :
        (state.push thermalFlip.channel).push thermalFlip.channel = state := by
      rw [← FinDist.push_comp]
      change state.push
        (GibbsPreserving.comp thermalFlip thermalFlip).channel = state
      rw [thermalFlip_involutive]
      exact FinDist.push_identity state
    have h := GibbsThermalObject.freeEnergyGap_monotone
      (X := gibbsThermalBit) (Y := gibbsThermalBit) rfl thermalFlip
      (state.push thermalFlip.channel)
    calc
      gibbsThermalBit.freeEnergyGap state =
          gibbsThermalBit.freeEnergyGap
            ((state.push thermalFlip.channel).push thermalFlip.channel) :=
        congrArg (fun next : FinDist thermalBit.system ↦
          gibbsThermalBit.freeEnergyGap next) hroundtrip.symm
      _ ≤ gibbsThermalBit.freeEnergyGap (state.push thermalFlip.channel) := h

/-- The equilibrium distribution of two independent thermal bits assigns
probability one quarter to every pair. -/
theorem thermal_pair_equilibrium (output : Bool × Bool) :
    (ThermalObject.tensor thermalBit thermalBit).equilibrium.prob output =
      (1 : ℚ≥0) / 4 := by
  rcases output with ⟨left, right⟩
  cases left <;> cases right <;>
    change ((1 : ℚ≥0) / 2) * (1 / 2) = 1 / 4 <;>
    norm_num

/-- The common-temperature Gibbs realization of two independent thermal
bits. -/
noncomputable def gibbsThermalPair : GibbsThermalObject :=
  gibbsThermalBit.tensor gibbsThermalBit rfl

/-- The pair's equilibrium free energy is twice the one-bit value. -/
theorem thermalPair_equilibriumFreeEnergy :
    gibbsThermalPair.equilibriumFreeEnergy = -2 * Real.log 2 := by
  rw [show gibbsThermalPair.equilibriumFreeEnergy =
      gibbsThermalBit.equilibriumFreeEnergy +
        gibbsThermalBit.equilibriumFreeEnergy by
    exact GibbsThermalObject.equilibriumFreeEnergy_tensor
      gibbsThermalBit gibbsThermalBit rfl,
    thermalBit_equilibriumFreeEnergy]
  ring

/-- Excess free energy of an independent pair is the sum of the two one-bit
excess free energies. -/
theorem thermalPair_freeEnergyGap_additive
    (p q : FinDist thermalBit.system) :
    gibbsThermalPair.freeEnergyGap (p.tensor q) =
      gibbsThermalBit.freeEnergyGap p +
        gibbsThermalBit.freeEnergyGap q := by
  exact GibbsThermalObject.freeEnergyGap_tensor
    gibbsThermalBit gibbsThermalBit rfl p q

-- The distinguished equilibrium state is exactly normalized.
#eval decide (∑ value : Bool, fairEquilibrium.prob value = 1)

-- Thermal bit flip is deterministic.
#eval decide (thermalFlip.channel.prob true false = 1)

-- Bit flip preserves the exact uniform equilibrium state.
#eval decide ((fairEquilibrium.push flipChannel).prob true = (1 : ℚ≥0) / 2)

-- The equilibrium distribution is executable as a free preparation.
#eval decide ((GibbsPreserving.equilibriumFreeState thermalBit).channel.prob
  PUnit.unit false = (1 : ℚ≥0) / 2)

-- Product equilibrium assigns exact probability one quarter to each pair.
#eval decide ((ThermalObject.tensor thermalBit thermalBit).equilibrium.prob
  (false, true) = (1 : ℚ≥0) / 4)

-- Serial composition computes two flips as the identity channel.
#eval decide ((GibbsPreserving.comp thermalFlip thermalFlip).channel.prob
  true true = 1)

end Ript.Examples.SimpleThermalModel
