import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Ript.Examples.ExactWorkErasure
import Ript.Models.Thermal.Protocol

/-!
# Exact closed erasure--recharge work cycle

This module closes the finite entropy-neutral work-erasure witness into an
executable two-step cycle.  The recharge step uses the free energy released
when an erased memory is randomized back to equilibrium to raise the pure
two-level battery from its low state to its high state.  Its exact rational
channel maps

`erased memory tensor pure low` to `fair memory tensor pure high`

while preserving the same joint Gibbs equilibrium as the erasure channel.
Composing erasure and recharge therefore returns the complete memory--battery
state exactly.  Each step attains the mechanical Landauer work balance, and
their signed system and battery energy changes sum to zero.  Thus this is a
closed work-storage cycle, not a net-work source.
-/

set_option autoImplicit false

namespace Ript.Examples.ExactWorkCycle

open Ript.Examples.SimpleThermalModel
open Ript.Examples.ExactWorkErasure
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Thermal

noncomputable section

/-- The joint operational thermal object containing the memory and work
battery throughout the closed cycle. -/
abbrev memoryBatteryThermal : ThermalObject :=
  ThermalObject.tensor thermalBit workBatteryThermal

/-- Exact recharge channel.  The erased/low state is split uniformly between
the two high-battery memory states.  The remaining rows restore exactly the
equilibrium mass needed on the two low-battery outputs. -/
def exactWorkRechargeChannel :
    FinStoch (Object.tensor bitSystem bitSystem)
      (Object.tensor bitSystem bitSystem) where
  prob := fun (input : Bool × Bool) (output : Bool × Bool) ↦
    if input = (false, false) then
      if output.2 then (1 : ℚ≥0) / 2 else 0
    else if input = (true, false) then
      if output = (false, false) then 1 else 0
    else
      if output = (true, false) then 1 else 0
  normalized := by
    rintro ⟨inputSystem, inputBattery⟩
    change Bool at inputSystem inputBattery
    change (∑ output : Bool × Bool,
      if (inputSystem, inputBattery) = (false, false) then
        (if output.2 then (1 : ℚ≥0) / 2 else 0)
      else if (inputSystem, inputBattery) = (true, false) then
        (if output = (false, false) then 1 else 0)
      else
        (if output = (true, false) then 1 else 0)) = 1
    rw [Fintype.sum_prod_type]
    repeat' rw [Fintype.sum_bool]
    cases inputSystem <;> cases inputBattery <;> norm_num

/-- The recharge channel preserves the product of the fair-memory and biased
work-battery Gibbs equilibria. -/
theorem exactWorkRechargeChannel_preserves_equilibrium :
    (fairEquilibrium.tensor workBatteryEquilibrium).push
        exactWorkRechargeChannel =
      fairEquilibrium.tensor workBatteryEquilibrium := by
  apply FinDist.ext
  rintro ⟨outputSystem, outputBattery⟩
  change Bool at outputSystem outputBattery
  change (∑ input : Bool × Bool,
    ((1 : ℚ≥0) / 2 *
      (if input.2 then (1 : ℚ≥0) / 3 else 2 / 3)) *
      (if input = (false, false) then
        (if outputBattery then (1 : ℚ≥0) / 2 else 0)
      else if input = (true, false) then
        (if (outputSystem, outputBattery) = (false, false) then 1 else 0)
      else
        (if (outputSystem, outputBattery) = (true, false) then 1 else 0))) =
    ((1 : ℚ≥0) / 2 *
      (if outputBattery then (1 : ℚ≥0) / 3 else 2 / 3))
  rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_bool]
  cases outputSystem <;> cases outputBattery <;> norm_num

/-- The exact recharge channel as a free process on the joint memory--battery
thermal object. -/
def exactWorkRechargeProcess :
    GibbsPreserving memoryBatteryThermal memoryBatteryThermal where
  channel := exactWorkRechargeChannel
  preserves_equilibrium := exactWorkRechargeChannel_preserves_equilibrium

/-- Randomizing the erased memory back to equilibrium recharges a pure low
battery to the pure high state exactly. -/
theorem exactWorkRechargeChannel_recharges :
    (erasedBit.tensor batteryLow).push exactWorkRechargeChannel =
      fairEquilibrium.tensor batteryHigh := by
  apply FinDist.ext
  rintro ⟨outputSystem, outputBattery⟩
  change Bool at outputSystem outputBattery
  change (∑ input : Bool × Bool,
    ((if false = input.1 then (1 : ℚ≥0) else 0) *
      (if false = input.2 then (1 : ℚ≥0) else 0)) *
      (if input = (false, false) then
        (if outputBattery then (1 : ℚ≥0) / 2 else 0)
      else if input = (true, false) then
        (if (outputSystem, outputBattery) = (false, false) then 1 else 0)
      else
        (if (outputSystem, outputBattery) = (true, false) then 1 else 0))) =
    ((1 : ℚ≥0) / 2 *
      (if true = outputBattery then (1 : ℚ≥0) else 0))
  rw [Fintype.sum_prod_type]
  repeat' rw [Fintype.sum_bool]
  cases outputSystem <;> cases outputBattery <;> norm_num

/-- Process-typed form of exact work erasure, stable under the joint thermal
object's dependent carrier projection. -/
theorem exactWorkErasureProcess_erases :
    (fairEquilibrium.tensor batteryHigh).push
        exactWorkErasureProcess.channel =
      erasedBit.tensor batteryLow :=
  exactWorkErasureChannel_erases

/-- Process-typed form of exact recharge, stable under the joint thermal
object's dependent carrier projection. -/
theorem exactWorkRechargeProcess_recharges :
    (erasedBit.tensor batteryLow).push
        exactWorkRechargeProcess.channel =
      fairEquilibrium.tensor batteryHigh :=
  exactWorkRechargeChannel_recharges

/-- Exact entropy-neutral work-assisted recharge transition at every positive
inverse temperature. -/
def exactWorkRecharge (beta : ℝ) (hbeta : 0 < beta) :
    WorkAssistedTransition
      (gibbsThermalBitAt beta hbeta)
      (gibbsThermalBitAt beta hbeta)
      (workBatteryAt beta hbeta) where
  sourceTemperature := rfl
  targetTemperature := rfl
  initialSystem := erasedBit
  finalSystem := fairEquilibrium
  initialBattery := batteryLow
  finalBattery := batteryHigh
  process := exactWorkRechargeProcess
  evolves := exactWorkRechargeChannel_recharges

/-- The recharge step also has entropy-neutral pure battery endpoints. -/
theorem exactWorkRecharge_batteryEntropy_neutral (beta : ℝ)
    (hbeta : 0 < beta) :
    (workBatteryAt beta hbeta).entropy
        (exactWorkRecharge beta hbeta).initialBattery =
      (workBatteryAt beta hbeta).entropy
        (exactWorkRecharge beta hbeta).finalBattery := by
  change (workBatteryAt beta hbeta).entropy batteryLow =
    (workBatteryAt beta hbeta).entropy batteryHigh
  exact (exactWorkErasure_batteryEntropy_neutral beta hbeta).symm

/-- Randomizing the erased memory releases exactly `log 2 / beta` of excess
free energy, so its signed free-energy increase is the negative quantity. -/
theorem exactWorkRecharge_systemFreeEnergyIncrease (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkRecharge beta hbeta).systemFreeEnergyIncrease =
      -(Real.log 2 / beta) := by
  unfold WorkAssistedTransition.systemFreeEnergyIncrease exactWorkRecharge
  rw [thermalBitAt_fair_freeEnergyGap,
    thermalBitAt_erased_freeEnergyGap]
  ring

/-- Raising the pure battery from low to high consumes exactly
`log 2 / beta`, so its signed energy decrease is the negative quantity. -/
theorem exactWorkRecharge_batteryEnergyDecrease (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkRecharge beta hbeta).batteryEnergyDecrease =
      -(Real.log 2 / beta) := by
  change (workBatteryAt beta hbeta).meanEnergy batteryLow -
    (workBatteryAt beta hbeta).meanEnergy batteryHigh =
      -(Real.log 2 / beta)
  have hDischarge := exactWorkErasure_battery_work beta hbeta
  change (workBatteryAt beta hbeta).meanEnergy batteryHigh -
    (workBatteryAt beta hbeta).meanEnergy batteryLow =
      Real.log 2 / beta at hDischarge
  calc
    (workBatteryAt beta hbeta).meanEnergy batteryLow -
        (workBatteryAt beta hbeta).meanEnergy batteryHigh =
      -((workBatteryAt beta hbeta).meanEnergy batteryHigh -
        (workBatteryAt beta hbeta).meanEnergy batteryLow) := by ring
    _ = -(Real.log 2 / beta) := congrArg Neg.neg hDischarge

/-- Equivalently, the recharge step raises battery mean energy by exactly
`log 2 / beta`. -/
theorem exactWorkRecharge_batteryEnergyIncrease (beta : ℝ)
    (hbeta : 0 < beta) :
    (workBatteryAt beta hbeta).meanEnergy
          (exactWorkRecharge beta hbeta).finalBattery -
        (workBatteryAt beta hbeta).meanEnergy
          (exactWorkRecharge beta hbeta).initialBattery =
      Real.log 2 / beta := by
  have hDecrease := exactWorkRecharge_batteryEnergyDecrease beta hbeta
  unfold WorkAssistedTransition.batteryEnergyDecrease at hDecrease
  linarith

/-- The recharge step attains the signed mechanical Landauer balance: memory
free-energy release exactly pays the work battery's energy increase. -/
theorem exactWorkRecharge_saturates_landauer_work (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkRecharge beta hbeta).systemFreeEnergyIncrease =
      (exactWorkRecharge beta hbeta).batteryEnergyDecrease := by
  rw [exactWorkRecharge_systemFreeEnergyIncrease,
    exactWorkRecharge_batteryEnergyDecrease]

/-- The generic entropy-neutral work theorem specializes to the exact
recharge transition. -/
theorem exactWorkRecharge_obeys_landauer_work (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkRecharge beta hbeta).systemFreeEnergyIncrease ≤
      (exactWorkRecharge beta hbeta).batteryEnergyDecrease :=
  (exactWorkRecharge beta hbeta).landauer_work_bound
    (exactWorkRecharge_batteryEntropy_neutral beta hbeta)

/-- Erasure followed by recharge is a finite closed protocol on the joint
memory--battery thermal object. -/
def exactWorkCycle : FiniteClosedProtocol memoryBatteryThermal where
  steps := [exactWorkErasureProcess, exactWorkRechargeProcess]

/-- The closed work cycle has the exact three-state trajectory
fair/high, erased/low, fair/high. -/
theorem exactWorkCycle_trace :
    exactWorkCycle.trace (fairEquilibrium.tensor batteryHigh) =
      [fairEquilibrium.tensor batteryHigh,
        erasedBit.tensor batteryLow,
        fairEquilibrium.tensor batteryHigh] :=
  FiniteClosedProtocol.trace_twoSteps
    exactWorkErasureProcess exactWorkRechargeProcess
    (fairEquilibrium.tensor batteryHigh) (erasedBit.tensor batteryLow)
    exactWorkErasureProcess_erases exactWorkRechargeProcess_recharges

/-- The two-step protocol returns the complete memory--battery state exactly. -/
theorem exactWorkCycle_returns :
    exactWorkCycle.run (fairEquilibrium.tensor batteryHigh) =
      fairEquilibrium.tensor batteryHigh :=
  FiniteClosedProtocol.run_twoSteps
    exactWorkErasureProcess exactWorkRechargeProcess
    (fairEquilibrium.tensor batteryHigh) (erasedBit.tensor batteryLow)
    exactWorkErasureProcess_erases exactWorkRechargeProcess_recharges

/-- The signed battery-energy changes of discharge and recharge cancel
exactly, ruling out any net-work interpretation of the closed cycle. -/
theorem exactWorkCycle_batteryEnergy_balanced (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkErasure beta hbeta).batteryEnergyDecrease +
        (exactWorkRecharge beta hbeta).batteryEnergyDecrease = 0 := by
  rw [exactWorkErasure_battery_work,
    exactWorkRecharge_batteryEnergyDecrease]
  ring

/-- The memory's signed free-energy changes also cancel exactly over the
closed cycle. -/
theorem exactWorkCycle_systemFreeEnergy_balanced (beta : ℝ)
    (hbeta : 0 < beta) :
    (exactWorkErasure beta hbeta).systemFreeEnergyIncrease +
        (exactWorkRecharge beta hbeta).systemFreeEnergyIncrease = 0 := by
  rw [exactWorkErasure_system_cost,
    exactWorkRecharge_systemFreeEnergyIncrease]
  ring

end


-- The erased/low input is split uniformly across the two high-battery memory
-- outputs.
#eval decide
  (exactWorkRechargeChannel.prob (false, false) (false, true) =
    (1 : ℚ≥0) / 2)

-- The closed protocol contains exactly erasure followed by recharge.
#eval decide (exactWorkCycle.steps.length = 2)

-- The low-erased state's mass follows the exact closed trace `0 -> 1 -> 0`.
#eval decide
  ((exactWorkCycle.trace (fairEquilibrium.tensor batteryHigh)).map
    (fun state ↦ state.prob (false, false)) = [(0 : ℚ≥0), 1, 0])

end Ript.Examples.ExactWorkCycle
