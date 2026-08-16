import Mathlib.Tactic.NormNum
import Ript.Models.Thermal.KLDivergence

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

/-- The equilibrium distribution of two independent thermal bits assigns
probability one quarter to every pair. -/
theorem thermal_pair_equilibrium (output : Bool × Bool) :
    (ThermalObject.tensor thermalBit thermalBit).equilibrium.prob output =
      (1 : ℚ≥0) / 4 := by
  rcases output with ⟨left, right⟩
  cases left <;> cases right <;>
    change ((1 : ℚ≥0) / 2) * (1 / 2) = 1 / 4 <;>
    norm_num

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
