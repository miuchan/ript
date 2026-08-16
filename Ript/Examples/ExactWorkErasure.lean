import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Ript.Examples.SimpleThermalModel
import Ript.Models.Thermal.Work

/-!
# Exact erasure paid by a finite entropy-neutral work battery

This module gives an executable existence and saturation witness for the
mechanical-work form of the finite Landauer bound.  The memory is the uniform
zero-energy Boolean Gibbs system.  The work battery is a nondegenerate Boolean
system whose exact equilibrium assigns mass `2/3` to its low state and `1/3`
to its high state.  At inverse temperature `beta`, its canonical energy gap is
exactly `log 2 / beta`.

The joint Gibbs-preserving channel sends either state with a high battery
deterministically to an erased memory and low battery.  Its remaining rows
redistribute equilibrium mass so the full channel stays Gibbs-preserving.  It
therefore maps

`fair memory tensor pure high` to `erased memory tensor pure low`.

Both battery endpoints are pure and hence have equal zero entropy.  The
battery mean-energy decrease and the memory free-energy increase are both
`log 2 / beta`, so the entropy-neutral Landauer work bound is attained exactly.
-/

set_option autoImplicit false

namespace Ript.Examples.ExactWorkErasure

open Ript.Examples.SimpleThermalModel
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Thermal

noncomputable section

/-- Exact two-level work-battery equilibrium: low state `false` has mass
`2/3`, and high state `true` has mass `1/3`. -/
def workBatteryEquilibrium : FinDist bitSystem where
  prob := fun state : Bool ↦ if state then (1 : ℚ≥0) / 3 else 2 / 3
  normalized := by
    change (∑ state : Bool,
      if state then (1 : ℚ≥0) / 3 else 2 / 3) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- The exact work-battery equilibrium has full support. -/
theorem workBatteryEquilibrium_fullSupport (state : bitSystem) :
    workBatteryEquilibrium.prob state ≠ 0 := by
  change Bool at state
  cases state <;> simp [workBatteryEquilibrium]

/-- Operational finite thermal object for the nondegenerate work battery. -/
def workBatteryThermal : ThermalObject where
  system := bitSystem
  equilibrium := workBatteryEquilibrium

/-- Canonical Gibbs realization of the work battery at positive inverse
temperature `beta`. -/
def workBatteryAt (beta : ℝ) (hbeta : 0 < beta) : GibbsThermalObject :=
  GibbsThermalObject.ofFullSupport workBatteryThermal beta hbeta
    workBatteryEquilibrium_fullSupport

/-- Exact pure low-energy battery state. -/
def batteryLow : FinDist workBatteryThermal.system :=
  FinDist.pure false

/-- Exact pure high-energy battery state. -/
def batteryHigh : FinDist workBatteryThermal.system :=
  FinDist.pure true

/-- Exact joint channel that discharges a high battery while erasing the
memory, and uses its other rows to preserve the joint Gibbs equilibrium. -/
def exactWorkErasureChannel :
    FinStoch (Object.tensor bitSystem bitSystem)
      (Object.tensor bitSystem bitSystem) where
  prob := fun (input : Bool × Bool) (output : Bool × Bool) ↦
    if input.2 then
      if output = (false, false) then 1 else 0
    else if input.1 then
      if output.2 then (1 : ℚ≥0) / 2 else 0
    else
      if output = (true, false) then 1 else 0
  normalized := by
    rintro ⟨inputSystem, inputBattery⟩
    change Bool at inputSystem inputBattery
    change (∑ output : Bool × Bool,
      if inputBattery then
        (if output = (false, false) then (1 : ℚ≥0) else 0)
      else if inputSystem then
        (if output.2 then (1 : ℚ≥0) / 2 else 0)
      else
        (if output = (true, false) then 1 else 0)) = 1
    rw [Fintype.sum_prod_type]
    repeat' rw [Fintype.sum_bool]
    cases inputSystem <;> cases inputBattery <;> norm_num

/-- The exact joint channel preserves the product of the fair memory
equilibrium and the biased work-battery equilibrium. -/
theorem exactWorkErasureChannel_preserves_equilibrium :
    (fairEquilibrium.tensor workBatteryEquilibrium).push
        exactWorkErasureChannel =
      fairEquilibrium.tensor workBatteryEquilibrium := by
  apply FinDist.ext
  rintro ⟨outputSystem, outputBattery⟩
  change Bool at outputSystem outputBattery
  change (∑ input : Bool × Bool,
    ((1 : ℚ≥0) / 2 *
      (if input.2 then (1 : ℚ≥0) / 3 else 2 / 3)) *
      (if input.2 then
        (if (outputSystem, outputBattery) = (false, false) then 1 else 0)
      else if input.1 then
        (if outputBattery then (1 : ℚ≥0) / 2 else 0)
      else
        (if (outputSystem, outputBattery) = (true, false) then 1 else 0))) =
    ((1 : ℚ≥0) / 2 *
      (if outputBattery then (1 : ℚ≥0) / 3 else 2 / 3))
  rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_bool]
  cases outputSystem <;> cases outputBattery <;> norm_num

/-- The exact work-erasure channel as a free process on memory and battery. -/
def exactWorkErasureProcess :
    GibbsPreserving
      (ThermalObject.tensor thermalBit workBatteryThermal)
      (ThermalObject.tensor thermalBit workBatteryThermal) where
  channel := exactWorkErasureChannel
  preserves_equilibrium := exactWorkErasureChannel_preserves_equilibrium

/-- A high pure battery is discharged to the low pure state while the fair
memory is erased exactly. -/
theorem exactWorkErasureChannel_erases :
    (fairEquilibrium.tensor batteryHigh).push exactWorkErasureChannel =
      erasedBit.tensor batteryLow := by
  apply FinDist.ext
  rintro ⟨outputSystem, outputBattery⟩
  change Bool at outputSystem outputBattery
  change (∑ input : Bool × Bool,
    ((1 : ℚ≥0) / 2 *
      (if true = input.2 then (1 : ℚ≥0) else 0)) *
      (if input.2 then
        (if (outputSystem, outputBattery) = (false, false) then 1 else 0)
      else if input.1 then
        (if outputBattery then (1 : ℚ≥0) / 2 else 0)
      else
        (if (outputSystem, outputBattery) = (true, false) then 1 else 0))) =
    ((if false = outputSystem then (1 : ℚ≥0) else 0) *
      (if false = outputBattery then 1 else 0))
  rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_bool]
  cases outputSystem <;> cases outputBattery <;> norm_num

/-- Exact entropy-neutral work-assisted erasure transition at every positive
inverse temperature. -/
def exactWorkErasure (beta : ℝ) (hbeta : 0 < beta) :
    WorkAssistedTransition
      (gibbsThermalBitAt beta hbeta)
      (gibbsThermalBitAt beta hbeta)
      (workBatteryAt beta hbeta) where
  sourceTemperature := rfl
  targetTemperature := rfl
  initialSystem := fairEquilibrium
  finalSystem := erasedBit
  initialBattery := batteryHigh
  finalBattery := batteryLow
  process := exactWorkErasureProcess
  evolves := exactWorkErasureChannel_erases

/-- The canonical biased battery has exact energy gap `log 2 / beta` from its
low state to its high state. -/
theorem workBattery_energyDifference (beta : ℝ) (hbeta : 0 < beta) :
    (workBatteryAt beta hbeta).gibbs.energy true -
        (workBatteryAt beta hbeta).gibbs.energy false =
      Real.log 2 / beta := by
  unfold workBatteryAt
  rw [GibbsThermalObject.ofFullSupport_energy workBatteryThermal beta hbeta
      workBatteryEquilibrium_fullSupport
      (show workBatteryThermal.system from true),
    GibbsThermalObject.ofFullSupport_energy workBatteryThermal beta hbeta
      workBatteryEquilibrium_fullSupport
      (show workBatteryThermal.system from false)]
  simp [workBatteryThermal, workBatteryEquilibrium]
  have hlogTwoThird :
      Real.log ((2 : ℝ) / 3) = Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0)]
  rw [hlogTwoThird]
  ring

/-- The work battery is genuinely nondegenerate: its high state has strictly
greater energy than its low state. -/
theorem workBattery_low_lt_high (beta : ℝ) (hbeta : 0 < beta) :
    (workBatteryAt beta hbeta).gibbs.energy false <
      (workBatteryAt beta hbeta).gibbs.energy true := by
  have hgap : 0 < Real.log 2 / beta :=
    div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hbeta
  rw [← workBattery_energyDifference beta hbeta] at hgap
  linarith

/-- The pure high and pure low battery endpoints are entropy-neutral. -/
theorem exactWorkErasure_batteryEntropy_neutral (beta : ℝ)
    (hbeta : 0 < beta) :
    (workBatteryAt beta hbeta).entropy
        (exactWorkErasure beta hbeta).initialBattery =
      (workBatteryAt beta hbeta).entropy
        (exactWorkErasure beta hbeta).finalBattery := by
  change (workBatteryAt beta hbeta).entropy batteryHigh =
    (workBatteryAt beta hbeta).entropy batteryLow
  change (workBatteryAt beta hbeta).entropy (FinDist.pure true) =
    (workBatteryAt beta hbeta).entropy (FinDist.pure false)
  rw [GibbsThermalObject.entropy_pure (workBatteryAt beta hbeta)
      (show (workBatteryAt beta hbeta).thermal.system from true),
    GibbsThermalObject.entropy_pure (workBatteryAt beta hbeta)
      (show (workBatteryAt beta hbeta).thermal.system from false)]

/-- Exact memory erasure raises excess free energy by `log 2 / beta`. -/
theorem exactWorkErasure_system_cost (beta : ℝ) (hbeta : 0 < beta) :
    (exactWorkErasure beta hbeta).systemFreeEnergyIncrease =
      Real.log 2 / beta := by
  unfold WorkAssistedTransition.systemFreeEnergyIncrease exactWorkErasure
  rw [thermalBitAt_erased_freeEnergyGap,
    thermalBitAt_fair_freeEnergyGap]
  ring

/-- The pure high-to-low battery transition supplies exactly
`log 2 / beta` of mean energy. -/
theorem exactWorkErasure_battery_work (beta : ℝ) (hbeta : 0 < beta) :
    (exactWorkErasure beta hbeta).batteryEnergyDecrease =
      Real.log 2 / beta := by
  change (workBatteryAt beta hbeta).meanEnergy batteryHigh -
    (workBatteryAt beta hbeta).meanEnergy batteryLow = Real.log 2 / beta
  change (workBatteryAt beta hbeta).meanEnergy (FinDist.pure true) -
    (workBatteryAt beta hbeta).meanEnergy (FinDist.pure false) =
      Real.log 2 / beta
  rw [GibbsThermalObject.meanEnergy_pure (workBatteryAt beta hbeta)
      (show (workBatteryAt beta hbeta).thermal.system from true),
    GibbsThermalObject.meanEnergy_pure (workBatteryAt beta hbeta)
      (show (workBatteryAt beta hbeta).thermal.system from false)]
  exact workBattery_energyDifference beta hbeta

/-- Battery free-energy decrease equals supplied mechanical work for the
entropy-neutral endpoints and is exactly `log 2 / beta`. -/
theorem exactWorkErasure_battery_freeEnergy_payment (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkErasure beta hbeta).batteryFreeEnergyDecrease =
      Real.log 2 / beta := by
  calc
    (exactWorkErasure beta hbeta).batteryFreeEnergyDecrease =
        (exactWorkErasure beta hbeta).batteryEnergyDecrease :=
      WorkAssistedTransition.batteryFreeEnergyDecrease_eq_energyDecrease
        (exactWorkErasure beta hbeta)
        (exactWorkErasure_batteryEntropy_neutral beta hbeta)
    _ = Real.log 2 / beta := exactWorkErasure_battery_work beta hbeta

/-- **Exact finite mechanical Landauer saturation.** The memory free-energy
increase equals the entropy-neutral battery's supplied mean energy. -/
theorem exactWorkErasure_saturates_landauer_work (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkErasure beta hbeta).systemFreeEnergyIncrease =
      (exactWorkErasure beta hbeta).batteryEnergyDecrease := by
  rw [exactWorkErasure_system_cost beta hbeta,
    exactWorkErasure_battery_work beta hbeta]

/-- The generic entropy-neutral work bound specializes to the equality
witnessed by the executable finite protocol. -/
theorem exactWorkErasure_obeys_landauer_work (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkErasure beta hbeta).systemFreeEnergyIncrease ≤
      (exactWorkErasure beta hbeta).batteryEnergyDecrease :=
  (exactWorkErasure beta hbeta).landauer_work_bound
    (exactWorkErasure_batteryEntropy_neutral beta hbeta)

end


-- A high battery input is routed deterministically to erased memory and low
-- battery.
#eval decide (exactWorkErasureChannel.prob (true, true) (false, false) = 1)

-- The compensating low-battery row splits equally across the two high-battery
-- outputs.
#eval decide
  (exactWorkErasureChannel.prob (true, false) (false, true) = (1 : ℚ≥0) / 2)

-- Exact erasure leaves no mass on a non-erased memory output.
#eval decide
  (((fairEquilibrium.tensor batteryHigh).push exactWorkErasureChannel).prob
    (true, false) = 0)

end Ript.Examples.ExactWorkErasure
