import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Ript.Examples.SimpleThermalModel
import Ript.Models.Thermal.Bath

/-!
# Exact erasure with an explicit finite bath and information battery

This executable witness separates three resources that are often conflated in
informal Landauer arguments.  A fair system bit, a fair bath bit, and an erased
battery bit undergo the deterministic permutation

`((system, bath), battery) ↦ ((battery, bath), system)`.

The system is erased exactly, the bath is returned exactly, and the battery
changes from erased to fair.  The global channel preserves the uniform Gibbs
state because it is a permutation.  Consequently the system's free-energy
increase is paid exactly by lost battery free energy.  The battery entropy is
not constant, so this witness is an information-battery protocol rather than
an entropy-neutral mechanical-work protocol.
-/

set_option autoImplicit false

namespace Ript.Examples.ExplicitBathErasure

open Ript.Examples.SimpleThermalModel
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Thermal

noncomputable section

/-- Three independently uniform thermal bits, nested as
`((system, bath), battery)`. -/
def tripleThermalBit : ThermalObject :=
  ThermalObject.tensor (ThermalObject.tensor thermalBit thermalBit) thermalBit

/-- Swap the system with the battery while leaving the bath fixed. -/
def bathBatterySwapChannel :
    FinStoch (Object.tensor (Object.tensor bitSystem bitSystem) bitSystem)
      (Object.tensor (Object.tensor bitSystem bitSystem) bitSystem) :=
  FinStoch.dirac fun input ↦ ((input.2, input.1.2), input.1.1)

/-- The three-bit swap preserves the independent uniform equilibrium exactly. -/
theorem bathBatterySwap_preserves_equilibrium :
    ((fairEquilibrium.tensor fairEquilibrium).tensor fairEquilibrium).push
        bathBatterySwapChannel =
      (fairEquilibrium.tensor fairEquilibrium).tensor fairEquilibrium := by
  apply FinDist.ext
  rintro ⟨⟨outputSystem, outputBath⟩, outputBattery⟩
  change Bool at outputSystem outputBath outputBattery
  change (∑ input : (Bool × Bool) × Bool,
    (((1 : ℚ≥0) / 2 * ((1 : ℚ≥0) / 2)) * ((1 : ℚ≥0) / 2)) *
      (if ((input.2, input.1.2), input.1.1) =
          ((outputSystem, outputBath), outputBattery) then 1 else 0)) =
    (((1 : ℚ≥0) / 2 * ((1 : ℚ≥0) / 2)) * ((1 : ℚ≥0) / 2))
  rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_bool]
  cases outputSystem <;> cases outputBath <;> cases outputBattery <;> norm_num

/-- The deterministic swap is a free process on the uniform three-bit Gibbs
object. -/
def bathBatterySwap : GibbsPreserving tripleThermalBit tripleThermalBit where
  channel := bathBatterySwapChannel
  preserves_equilibrium := bathBatterySwap_preserves_equilibrium

/-- The global swap takes fair system and bath bits plus an erased battery to
an erased system and returned fair bath plus a fair battery. -/
theorem bathBatterySwap_erases :
    ((fairEquilibrium.tensor fairEquilibrium).tensor erasedBit).push
        bathBatterySwapChannel =
      (erasedBit.tensor fairEquilibrium).tensor fairEquilibrium := by
  apply FinDist.ext
  rintro ⟨⟨outputSystem, outputBath⟩, outputBattery⟩
  change Bool at outputSystem outputBath outputBattery
  change (∑ input : (Bool × Bool) × Bool,
    (((1 : ℚ≥0) / 2 * ((1 : ℚ≥0) / 2) *
        (if false = input.2 then 1 else 0)) *
      (if ((input.2, input.1.2), input.1.1) =
          ((outputSystem, outputBath), outputBattery) then 1 else 0))) =
    ((if false = outputSystem then 1 else 0) * ((1 : ℚ≥0) / 2) *
      ((1 : ℚ≥0) / 2))
  rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_bool]
  cases outputSystem <;> cases outputBath <;> cases outputBattery <;> norm_num

/-- An exact finite bath-assisted erasure protocol at every positive inverse
temperature. -/
def explicitBathErasure (beta : ℝ) (hbeta : 0 < beta) :
    BathAssistedTransition
      (gibbsThermalBitAt beta hbeta)
      (gibbsThermalBitAt beta hbeta)
      (gibbsThermalBitAt beta hbeta)
      (gibbsThermalBitAt beta hbeta) where
  sourceBathTemperature := rfl
  targetBathTemperature := rfl
  sourceBatteryTemperature := rfl
  targetBatteryTemperature := rfl
  initialSystem := fairEquilibrium
  finalSystem := erasedBit
  initialBath := fairEquilibrium
  finalBath := fairEquilibrium
  initialBattery := erasedBit
  finalBattery := fairEquilibrium
  process := bathBatterySwap
  evolves := bathBatterySwap_erases

/-- The explicit bath is returned to exactly its initial state. -/
theorem explicitBathErasure_bath_returns (beta : ℝ) (hbeta : 0 < beta) :
    (explicitBathErasure beta hbeta).finalBath =
      (explicitBathErasure beta hbeta).initialBath :=
  rfl

/-- Exact system erasure raises excess free energy by `log 2 / beta`. -/
theorem explicitBathErasure_system_cost (beta : ℝ) (hbeta : 0 < beta) :
    (explicitBathErasure beta hbeta).systemFreeEnergyIncrease =
      Real.log 2 / beta := by
  unfold BathAssistedTransition.systemFreeEnergyIncrease explicitBathErasure
  rw [thermalBitAt_erased_freeEnergyGap,
    thermalBitAt_fair_freeEnergyGap]
  ring

/-- Discharging the information battery loses exactly `log 2 / beta` of
excess free energy. -/
theorem explicitBathErasure_battery_payment (beta : ℝ)
    (hbeta : 0 < beta) :
    (explicitBathErasure beta hbeta).batteryFreeEnergyDecrease =
      Real.log 2 / beta := by
  unfold BathAssistedTransition.batteryFreeEnergyDecrease explicitBathErasure
  rw [thermalBitAt_erased_freeEnergyGap,
    thermalBitAt_fair_freeEnergyGap]
  ring

/-- The finite bath-assisted Landauer free-energy bound is saturated by the
explicit permutation protocol. -/
theorem explicitBathErasure_saturates (beta : ℝ) (hbeta : 0 < beta) :
    (explicitBathErasure beta hbeta).systemFreeEnergyIncrease =
      (explicitBathErasure beta hbeta).batteryFreeEnergyDecrease := by
  rw [explicitBathErasure_system_cost beta hbeta,
    explicitBathErasure_battery_payment beta hbeta]

/-- The information battery changes entropy from zero to `log 2`; hence the
protocol must not be reported as entropy-neutral mechanical work. -/
theorem explicitBathErasure_batteryEntropy_changes (beta : ℝ)
    (hbeta : 0 < beta) :
    (gibbsThermalBitAt beta hbeta).entropy
        (explicitBathErasure beta hbeta).initialBattery ≠
      (gibbsThermalBitAt beta hbeta).entropy
        (explicitBathErasure beta hbeta).finalBattery := by
  rw [show (explicitBathErasure beta hbeta).initialBattery = erasedBit by rfl,
    show (explicitBathErasure beta hbeta).finalBattery = fairEquilibrium by rfl,
    erasedBit_entropy, thermalBitAt_fair_entropy]
  exact ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- The abstract bath-return bound specializes to the equality witnessed
above. -/
theorem explicitBathErasure_obeys_landauer (beta : ℝ) (hbeta : 0 < beta) :
    (explicitBathErasure beta hbeta).systemFreeEnergyIncrease ≤
      (explicitBathErasure beta hbeta).batteryFreeEnergyDecrease :=
  (explicitBathErasure beta hbeta).landauer_freeEnergy_bound_of_bath_returns
    (explicitBathErasure_bath_returns beta hbeta)

end

-- The permutation routes an erased battery bit into the system output.
#eval decide (bathBatterySwapChannel.prob ((true, false), false)
  ((false, false), true) = 1)

-- The exact evolved state assigns probability one half to each battery value
-- when the erased system and fair bath output are fixed.
#eval decide
  ((((fairEquilibrium.tensor fairEquilibrium).tensor erasedBit).push
      bathBatterySwapChannel).prob ((false, true), true) = (1 : ℚ≥0) / 4)

-- No output with a non-erased system bit occurs.
#eval decide
  ((((fairEquilibrium.tensor fairEquilibrium).tensor erasedBit).push
      bathBatterySwapChannel).prob ((true, false), false) = 0)

end Ript.Examples.ExplicitBathErasure
